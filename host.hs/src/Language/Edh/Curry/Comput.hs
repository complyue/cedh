{-# LANGUAGE AllowAmbiguousTypes #-}

module Language.Edh.Curry.Comput where

import Control.Concurrent.STM
import Control.Monad
import Data.Dynamic
import qualified Data.Lossless.Decimal as D
import Data.Maybe
import Data.Proxy
import Data.Text (Text)
import qualified Data.Text as T
import Data.Typeable
import Data.Unique
import GHC.Conc (unsafeIOToSTM)
import Language.Edh.Curry.Shim
import Language.Edh.EHI
import Prelude

type AnnoText = Text

-- | An argument to be applied via formal application
--
-- The annotation text is for display purpose, it'd better correspond to some
-- class name as in the scripting environment, but not strictly enforced so.
--
-- The converter is responsible to convert arbitrary Edh value to a host value
-- wrapped as a 'Dynamic', when a matching argument is applied by scripting.
data AppliedArg
  = AppliedArg
      !AnnoText
      !AttrKey
      (EdhThreadState -> EdhValue -> (EdhValue -> Dynamic -> STM ()) -> STM ())

-- | An argument to be additionally applied per each actual call
--
-- The extractor is responsible to obtain the effect argument value from
-- current environment, each time the underlying computation is called.
data EffectfulArg
  = EffectfulArg
      !AnnoText
      !AttrKey
      (EdhThreadState -> (EdhValue -> Dynamic -> STM ()) -> STM ())

appliedCountArg :: AttrKey -> AppliedArg
appliedCountArg = appliedCountArg' "positive!int!DecimalType"

appliedCountArg' :: AnnoText -> AttrKey -> AppliedArg
appliedCountArg' !anno !argName = AppliedArg anno argName $
  \ !ets !val !exit -> case edhUltimate val of
    EdhDecimal !d | d >= 1 -> case D.decimalToInteger d of
      Just !i -> exit val $ toDyn (fromInteger i :: Int)
      Nothing -> edhValueDesc ets val $ \ !badDesc ->
        throwEdh ets UsageError $
          anno <> " as positive number expected but given: " <> badDesc
    _ -> edhValueDesc ets val $ \ !badDesc ->
      throwEdh ets UsageError $
        anno <> " as positive number expected but given: " <> badDesc

appliedIntArg :: AttrKey -> AppliedArg
appliedIntArg = appliedIntArg' "int!DecimalType"

appliedIntArg' :: AnnoText -> AttrKey -> AppliedArg
appliedIntArg' !anno !argName = AppliedArg anno argName $
  \ !ets !val !exit -> case edhUltimate val of
    EdhDecimal !d -> case D.decimalToInteger d of
      Just !i -> exit val $ toDyn (fromInteger i :: Int)
      Nothing -> edhValueDesc ets val $ \ !badDesc ->
        throwEdh ets UsageError $
          anno <> " as integer expected but given: " <> badDesc
    _ -> edhValueDesc ets val $ \ !badDesc ->
      throwEdh ets UsageError $
        anno <> " as integer expected but given: " <> badDesc

appliedDoubleArg :: AttrKey -> AppliedArg
appliedDoubleArg = appliedDoubleArg' "DecimalType"

appliedDoubleArg' :: AnnoText -> AttrKey -> AppliedArg
appliedDoubleArg' !anno !argName = AppliedArg anno argName $
  \ !ets !val !exit -> case edhUltimate val of
    EdhDecimal !d -> exit val $ toDyn (fromRational (toRational d) :: Double)
    _ -> edhValueDesc ets val $ \ !badDesc ->
      throwEdh ets UsageError $
        anno <> " as number expected but given: " <> badDesc

performDoubleArg :: AttrKey -> EffectfulArg
performDoubleArg !argName =
  performDoubleArg' "DecimalType" argName $
    const $
      throwEdhTx UsageError $
        "missing effectful argument: " <> attrKeyStr argName

performDoubleArg' ::
  AnnoText ->
  AttrKey ->
  (((EdhValue, Double) -> EdhTx) -> EdhTx) ->
  EffectfulArg
performDoubleArg' !anno !argName !effDefault =
  EffectfulArg anno argName $ \ !ets !exit ->
    runEdhTx ets $
      performEdhEffect' argName $ \ !maybeVal _ets ->
        case edhUltimate <$> maybeVal of
          Nothing ->
            runEdhTx ets $ effDefault $ \(!v, !d) _ets -> exit v $ toDyn d
          Just !val -> do
            let badArg = edhValueDesc ets val $ \ !badDesc ->
                  throwEdh ets UsageError $
                    "effectful number expected but given: "
                      <> badDesc
            case edhUltimate val of
              EdhDecimal !d ->
                exit val $ toDyn (fromRational (toRational d) :: Double)
              _ -> badArg

appliedHostArg :: forall t. Typeable t => AttrKey -> AppliedArg
appliedHostArg !argName = appliedHostArg' @t typeName argName $
  \ !val _obj !d !exit -> exitEdhTx exit (val, toDyn d)
  where
    typeName = T.pack $ show $ typeRep (Proxy :: Proxy t)

appliedHostArg' ::
  forall t.
  Typeable t =>
  AnnoText ->
  AttrKey ->
  (EdhValue -> Object -> t -> EdhTxExit (EdhValue, Dynamic) -> EdhTx) ->
  AppliedArg
appliedHostArg' !typeName !argName !dmap = AppliedArg typeName argName $
  \ !ets !val !exit -> do
    let badArg = edhValueDesc ets val $ \ !badDesc ->
          throwEdh ets UsageError $
            "host " <> typeName <> " object expected but given: " <> badDesc
    case edhUltimate val of
      EdhObject !obj -> case edh'obj'store obj of
        HostStore !dd -> case fromDynamic dd of
          Just !comput ->
            case comput'thunk comput of
              Effected !effected -> case fromDynamic effected of
                Just (d :: t) -> runEdhTx ets $
                  dmap val obj d $ \(!val', !dd') _ets -> exit val' dd'
                Nothing -> badArg
              Applied !applied | null (comput'effectful'args comput) ->
                case fromDynamic applied of
                  Just (d :: t) -> runEdhTx ets $
                    dmap val obj d $ \(!val', !dd') _ets -> exit val' dd'
                  Nothing -> badArg
              _ -> edhValueDesc ets val $ \ !badDesc ->
                throwEdh ets UsageError $
                  "comput given for " <> attrKeyStr argName
                    <> " not effected, it is: "
                    <> badDesc
          Nothing -> case fromDynamic dd of
            Just (d :: t) -> runEdhTx ets $
              dmap val obj d $ \(!val', !dd') _ets -> exit val' dd'
            Nothing -> badArg
        _ -> badArg
      _ -> badArg

performHostArg :: forall t. Typeable t => AttrKey -> EffectfulArg
performHostArg !argName =
  performHostArg' @t typeName argName $
    const $
      throwEdhTx UsageError $
        "missing effectful argument: " <> attrKeyStr argName
  where
    typeName = T.pack $ show $ typeRep (Proxy :: Proxy t)

performHostArg' ::
  forall t.
  Typeable t =>
  AnnoText ->
  AttrKey ->
  (((EdhValue, t) -> EdhTx) -> EdhTx) ->
  EffectfulArg
performHostArg' !typeName !argName !effDefault =
  performHostArg''' typeName argName effDefault $
    \ !val _obj !d !exit -> exitEdhTx exit (val, toDyn d)

performHostArg'' ::
  forall t.
  Typeable t =>
  AnnoText ->
  AttrKey ->
  (EdhValue -> Object -> t -> EdhTxExit (EdhValue, Dynamic) -> EdhTx) ->
  EffectfulArg
performHostArg'' !typeName !argName !dmap =
  performHostArg''' @t typeName argName effDefault dmap
  where
    effDefault =
      const $
        throwEdhTx UsageError $
          "missing effectful argument: " <> attrKeyStr argName

performHostArg''' ::
  forall t.
  Typeable t =>
  AnnoText ->
  AttrKey ->
  (((EdhValue, t) -> EdhTx) -> EdhTx) ->
  (EdhValue -> Object -> t -> EdhTxExit (EdhValue, Dynamic) -> EdhTx) ->
  EffectfulArg
performHostArg''' !typeName !argName !effDefault !dmap =
  EffectfulArg typeName argName $ \ !ets !exit ->
    runEdhTx ets $
      performEdhEffect' argName $ \ !maybeVal _ets ->
        case edhUltimate <$> maybeVal of
          Nothing ->
            runEdhTx ets $ effDefault $ \(!v, !d) _ets -> exit v $ toDyn d
          Just !val -> do
            let badArg = edhValueDesc ets val $ \ !badDesc ->
                  throwEdh ets UsageError $
                    "effectful host " <> typeName
                      <> " object expected but given: "
                      <> badDesc
            case edhUltimate val of
              EdhObject !obj -> case edh'obj'store obj of
                HostStore !dd -> case fromDynamic dd of
                  Just !comput ->
                    case comput'thunk comput of
                      Effected !effected -> case fromDynamic effected of
                        Just (d :: t) ->
                          runEdhTx ets $
                            dmap val obj d $
                              \(!val', !dd') _ets -> exit val' dd'
                        Nothing -> badArg
                      Applied !applied | null (comput'effectful'args comput) ->
                        case fromDynamic applied of
                          Just (d :: t) ->
                            runEdhTx ets $
                              dmap val obj d $
                                \(!val', !dd') _ets -> exit val' dd'
                          Nothing -> badArg
                      _ -> edhValueDesc ets val $ \ !badDesc ->
                        throwEdh ets UsageError $
                          "comput given for " <> attrKeyStr argName
                            <> " not effected, it is: "
                            <> badDesc
                  Nothing -> case fromDynamic dd of
                    Just (d :: t) ->
                      runEdhTx ets $
                        dmap val obj d $ \(!val', !dd') _ets -> exit val' dd'
                    Nothing -> badArg
                _ -> badArg
              _ -> badArg

computArgDefault ::
  forall t. Typeable t => Object -> (((EdhValue, t) -> EdhTx) -> EdhTx)
computArgDefault = computArgDefault' []

computArgDefault' ::
  forall t.
  Typeable t =>
  [EdhValue] ->
  Object ->
  (((EdhValue, t) -> EdhTx) -> EdhTx)
computArgDefault' = flip computArgDefault'' []

computArgDefault'' ::
  forall t.
  Typeable t =>
  [EdhValue] ->
  [(AttrKey, EdhValue)] ->
  Object ->
  (((EdhValue, t) -> EdhTx) -> EdhTx)
computArgDefault'' !args !kwargs !clsComput !exit =
  constructComput'' args kwargs clsComput $ \(!obj, !thunk) -> case thunk of
    Effected !effected -> case fromDynamic effected of
      Just (d :: t) -> exit (EdhObject obj, d)
      Nothing -> error "bug: wrong host type constructed from a comput class"
    _ -> error "bug: a comput class based default arg value ctor not effecting"

-- | Computation to be performed
--
-- todo the constructors should be hidden, with ctor functions available to
--      the users
data ComputTBP
  = ComputDone !Dynamic
  | ComputIO !Dynamic
  | ComputIO' !(IO Dynamic)
  | ComputSTM !Dynamic
  | ComputSTM' !(STM Dynamic)
  | ComputEdh (EdhThreadState -> (Dynamic -> STM ()) -> STM ())
  | ComputEdhSTM (EdhTxExit EdhValue -> EdhTx)
  | ComputEdhIO (EdhThreadState -> IO EdhValue)
  | InflateEdh (EdhThreadState -> (Dynamic -> KwArgs -> STM ()) -> STM ())

computDone :: forall a. Typeable a => a -> ComputTBP
computDone = ComputDone . toDyn

computIO :: forall a. Typeable a => IO a -> ComputTBP
computIO = ComputIO . toDyn

computIO' :: IO Dynamic -> ComputTBP
computIO' = ComputIO'

computSTM :: forall a. Typeable a => STM a -> ComputTBP
computSTM = ComputSTM . toDyn

computSTM' :: STM Dynamic -> ComputTBP
computSTM' = ComputSTM'

computEdh ::
  forall a.
  Typeable a =>
  (EdhThreadState -> (a -> STM ()) -> STM ()) ->
  ComputTBP
computEdh !c = ComputEdh $ \ !ets !exit -> c ets $ \ !a -> exit (toDyn a)

computEdh' ::
  (EdhThreadState -> (Dynamic -> STM ()) -> STM ()) ->
  ComputTBP
computEdh' = ComputEdh

-- | Result can't be returned on comput object construction, while the
-- constructed comput object can always mult-shot by subsequent calls
computEdhSTM :: (EdhTxExit EdhValue -> EdhTx) -> ComputTBP
computEdhSTM = ComputEdhSTM

-- | Result can't be returned on comput object construction, while the
-- constructed comput object can always mult-shot by subsequent calls
computEdhIO :: (EdhThreadState -> IO EdhValue) -> ComputTBP
computEdhIO = ComputEdhIO

inflateEdh ::
  (EdhThreadState -> (Dynamic -> KwArgs -> STM ()) -> STM ()) ->
  ComputTBP
inflateEdh = InflateEdh

-- | The thunk of a computation can be in 3 different stages:
-- - Unapplied
--   - Only partial formal arguments have been collected,
--     the thunk has not been applied at all.
-- - Applied
--   - All formal arguments have been collected,
--     the thunk has been applied with all formal arguments, but not with
--     effectful arguments.
-- - Effected
--   - A fully applied computation has been called, this is the result,
--     the thunk is the result from a fully applied Comput get called,
--     effectful arguments have been collected and applied as well.
data ComputThunk = Unapplied !Dynamic | Applied !Dynamic | Effected !Dynamic

-- | Everything in Haskell is a computation, let's make everything scriptable
--
-- And with dynamic effects
data Comput = Comput
  { -- | Thunk in possibly different stages
    comput'thunk :: !ComputThunk,
    -- | Formal arguments to be applied, with all or partial values collected
    comput'applied'args :: ![(AppliedArg, Maybe (EdhValue, Dynamic))],
    -- | Effectful arguments to be additionally applied per each call, with
    -- values collected in case of an effected computation.
    comput'effectful'args :: ![(EffectfulArg, Maybe (EdhValue, Dynamic))],
    -- | Results the computation actively yielded as it was effected
    comput'results :: KwArgs
  }

takeComputEffect ::
  Dynamic ->
  EdhThreadState ->
  (Either (Dynamic, KwArgs) EdhValue -> STM ()) ->
  STM ()
takeComputEffect !effected !ets !exit = case fromDynamic effected of
  Nothing -> exit $ Left (effected, odEmpty)
  Just (tbp :: ComputTBP) -> case tbp of
    ComputDone !done -> exit $ Left (done, odEmpty)
    ComputIO !dynIO ->
      runEdhTx ets $
        edhContIO $
          dynPerformIO dynTypeBug dynIO >>= \ !effected' ->
            atomically $ exit $ Left (effected', odEmpty)
    ComputIO' !ioa ->
      runEdhTx ets $
        edhContIO $
          ioa >>= \ !effected' ->
            atomically $ exit $ Left (effected', odEmpty)
    ComputSTM !dynSTM ->
      edhContSTM'' ets $
        dynPerformSTM dynTypeBug dynSTM
          >>= \ !effected' -> exit $ Left (effected', odEmpty)
    ComputSTM' !stma ->
      edhContSTM'' ets $
        stma >>= \ !effected' -> exit $ Left (effected', odEmpty)
    ComputEdh !act ->
      act ets $ \ !effected' -> exit $ Left (effected', odEmpty)
    ComputEdhSTM !act ->
      runEdhTx ets $ act $ \ !result _ets -> exit $ Right result
    ComputEdhIO !act ->
      runEdhTx ets $
        edhContIO $ act ets >>= \ !result -> atomically $ exit $ Right result
    InflateEdh !act ->
      act ets $ \ !effected' !results -> exit $ Left (effected', results)
  where
    dynTypeBug = error "bug: comput dyn type mismatch"

applyComputArgs ::
  Comput ->
  EdhThreadState ->
  ArgsPack ->
  (Comput -> STM ()) ->
  STM ()
applyComputArgs
  comput@(Comput !thunk !appliedArgs !effectfulArgs !results)
  !ets
  apk@(ArgsPack !args !kwargs)
  !exit = case thunk of
    Unapplied !unapplied -> applyArgs appliedArgs $ \ !appliedArgs' ->
      allApplied [] appliedArgs' >>= \case
        Nothing -> exit $ Comput thunk appliedArgs' effectfulArgs results
        Just !dds -> case hostApply dds unapplied of
          Just !applied ->
            exit $ Comput (Applied applied) appliedArgs' effectfulArgs results
          Nothing ->
            throwEdh ets UsageError "some computation argument not applicable"
    Applied {} ->
      if null args && odNull kwargs
        then exit comput
        else edhValueRepr ets (EdhArgsPack apk) $ \ !badRepr ->
          throwEdh ets UsageError $
            "extranenous args to applied comput result:" <> badRepr
    Effected {} ->
      throwEdh ets UsageError "you don't call already effected computation"
    where
      hostApply :: [Dynamic] -> Dynamic -> Maybe Dynamic
      hostApply [] !df = Just df
      hostApply (a : as) !df = dynApply df a >>= hostApply as

      allApplied ::
        [Dynamic] ->
        [(AppliedArg, Maybe (EdhValue, Dynamic))] ->
        STM (Maybe [Dynamic])
      allApplied got [] = return $ Just $! reverse got
      allApplied _ ((_, Nothing) : _) = return Nothing
      allApplied got ((_, Just (_, dd)) : rest) = allApplied (dd : got) rest

      applyArgs ::
        [(AppliedArg, Maybe (EdhValue, Dynamic))] ->
        ([(AppliedArg, Maybe (EdhValue, Dynamic))] -> STM ()) ->
        STM ()
      applyArgs !pending !apkApplied =
        applyKwArgs [] pending kwargs
        where
          applyPosArgs ::
            [(AppliedArg, Maybe (EdhValue, Dynamic))] ->
            [(AppliedArg, Maybe (EdhValue, Dynamic))] ->
            [EdhValue] ->
            STM ()
          applyPosArgs passedArgs pendingArgs [] =
            apkApplied $! reverse passedArgs ++ pendingArgs
          applyPosArgs _ [] !extraArgs =
            edhValueRepr ets (EdhArgsPack $ ArgsPack extraArgs odEmpty) $
              \ !badApkRepr ->
                throwEdh ets UsageError $ "extraneous args: " <> badApkRepr
          applyPosArgs doneArgs (doneArg@(_, Just {}) : restArgs) pas =
            applyPosArgs (doneArg : doneArgs) restArgs pas
          applyPosArgs
            doneArgs
            ((aa@(AppliedArg _anno _name !cnvt), Nothing) : restArgs)
            (pa : pas') =
              cnvt ets pa $ \ !av !dd ->
                applyPosArgs ((aa, Just (av, dd)) : doneArgs) restArgs pas'

          applyKwArgs ::
            [(AppliedArg, Maybe (EdhValue, Dynamic))] ->
            [(AppliedArg, Maybe (EdhValue, Dynamic))] ->
            KwArgs ->
            STM ()
          applyKwArgs passedArgs pendingArgs !kwas
            | odNull kwas =
              applyPosArgs [] (reverse passedArgs ++ pendingArgs) args
            | otherwise = matchKwArgs passedArgs pendingArgs
            where
              matchKwArgs ::
                [(AppliedArg, Maybe (EdhValue, Dynamic))] ->
                [(AppliedArg, Maybe (EdhValue, Dynamic))] ->
                STM ()
              matchKwArgs _ [] =
                edhValueRepr ets (EdhArgsPack $ ArgsPack [] kwas) $
                  \ !badApkRepr ->
                    throwEdh ets UsageError $
                      "extraneous kwargs: " <> badApkRepr
              matchKwArgs doneArgs (doneArg@(_, Just {}) : restArgs) =
                matchKwArgs (doneArg : doneArgs) restArgs
              matchKwArgs
                doneArgs
                ( doneArg@(aa@(AppliedArg _anno !name !cnvt), Nothing)
                    : restArgs
                  ) =
                  case odTakeOut name kwas of
                    (Nothing, kwas') ->
                      applyKwArgs (doneArg : doneArgs) restArgs kwas'
                    (Just !val, kwas') -> cnvt ets val $ \ !av !dd ->
                      applyKwArgs
                        ((aa, Just (av, dd)) : doneArgs)
                        restArgs
                        kwas'

-- | Construct a computation instance with no args
constructComput :: Object -> ((Object, ComputThunk) -> EdhTx) -> EdhTx
constructComput = constructComput' []

-- | Construct a computation instance with positional args
constructComput' :: [EdhValue] -> Object -> ((Object, ComputThunk) -> EdhTx) -> EdhTx
constructComput' = flip constructComput'' []

-- | Construct a computation instance with positional and keyword args
constructComput'' ::
  [EdhValue] ->
  [(AttrKey, EdhValue)] ->
  Object ->
  ((Object, ComputThunk) -> EdhTx) ->
  EdhTx
constructComput'' !args !kwargs !clsComput !exit =
  edhConstructObj clsComput (ArgsPack args $ odFromList kwargs) $
    \ !obj !ets ->
      castObjSelfStore obj >>= \case
        Nothing -> edhValueDesc ets (EdhObject clsComput) $ \ !badDesc ->
          throwEdh ets UsageError $ "not a comput class" <> badDesc
        Just !comput ->
          runEdhTx ets $ exit (obj, comput'thunk comput)

createComputClass ::
  Typeable t =>
  AttrName ->
  [AppliedArg] ->
  [EffectfulArg] ->
  t ->
  Scope ->
  STM Object
createComputClass !clsName !ctorAppArgs = \case
  [] -> createComputClass' clsName ctorAppArgs Nothing
  !ctorEffArgs -> createComputClass' clsName ctorAppArgs (Just ctorEffArgs)

createComputClass' ::
  Typeable t =>
  AttrName ->
  [AppliedArg] ->
  -- 'Nothing' means taking effect on ctor if fully applied,
  -- 'Just []' means with subsequent calls to take effect.
  Maybe [EffectfulArg] ->
  t ->
  Scope ->
  STM Object
createComputClass'
  !clsName
  !ctorAppArgs
  !needEffects
  !hostComput
  !clsOuterScope =
    mkHostClass clsOuterScope clsName computAllocator [] $
      \ !clsScope -> do
        !mths <-
          sequence $
            [ (AttrByName nm,) <$> mkHostProc clsScope vc nm hp
              | (nm, vc, hp) <-
                  [ ("(@)", EdhMethod, wrapHostProc argReadProc),
                    ("([])", EdhMethod, wrapHostProc argReadProc),
                    ("__repr__", EdhMethod, (reprProc, PackReceiver [])),
                    ("__show__", EdhMethod, (showProc, PackReceiver [])),
                    -- ("__desc__", EdhMethod, (descProc, PackReceiver [])),
                    ("__call__", EdhMethod, (callProc, WildReceiver))
                  ]
            ]
        iopdUpdate mths $ edh'scope'entity clsScope
    where
      computAllocator :: ArgsPack -> EdhObjectAllocator
      computAllocator !apk !ctorExit !etsCtor = do
        let !comput =
              Comput
                (Unapplied $ toDyn hostComput)
                ((,Nothing) <$> ctorAppArgs)
                (maybe [] ((,Nothing) <$>) needEffects)
                odEmpty
        applyComputArgs comput etsCtor apk $ \ !comput' ->
          case comput'thunk comput' of
            Applied !applied -> case needEffects of
              Just {} ->
                -- to be subsequently called after ctor, in effectful context
                ctorExit Nothing $ HostStore $ toDyn comput'
              Nothing -> takeComputEffect applied etsCtor $ \case
                Left (!effected, !results) ->
                  -- effect on ctor is final, this is a one-shot computation
                  ctorExit Nothing $
                    HostStore $
                      toDyn
                        comput'
                          { comput'thunk = Effected effected,
                            comput'results = results
                          }
                Right _result ->
                  -- one effect shot is taken on ctor,
                  -- subsequent calls can further take more multi-shots
                  ctorExit Nothing $ HostStore $ toDyn comput'
            _ ->
              -- leave it effected, or not fully applied
              ctorExit Nothing $ HostStore $ toDyn comput'

      -- Obtain an argument by name
      argReadProc :: EdhValue -> EdhHostProc
      argReadProc !keyVal !exit !ets = withThisHostObj ets $
        \(Comput _thunk !appliedArgs effArgs !results) ->
          edhValueAsAttrKey ets keyVal $ \ !argKey ->
            case odLookup argKey results of
              Just !val -> exitEdh ets exit val
              Nothing -> do
                let --

                    matchAppArg ::
                      STM () ->
                      STM ()
                    matchAppArg !naExit = match appliedArgs
                      where
                        match ::
                          [(AppliedArg, Maybe (EdhValue, Dynamic))] -> STM ()
                        match [] = naExit
                        match ((AppliedArg _anno !name _, ad) : rest) =
                          if name == argKey
                            then case ad of
                              Just (av, _d) -> exitEdh ets exit av
                              Nothing -> exitEdh ets exit edhNothing
                            else match rest

                    matchEffArg :: STM () -> STM ()
                    matchEffArg !naExit = match effArgs
                      where
                        match ::
                          [(EffectfulArg, Maybe (EdhValue, Dynamic))] -> STM ()
                        match [] = naExit
                        match ((_, Nothing) : rest) = match rest
                        match ((EffectfulArg _anno !name _, ad) : rest) =
                          if name == argKey
                            then case ad of
                              Just (av, _d) -> exitEdh ets exit av
                              Nothing -> exitEdh ets exit edhNothing
                            else match rest

                matchAppArg $ matchEffArg $ exitEdh ets exit edhNA

      reprProc :: ArgsPack -> EdhHostProc
      reprProc _ !exit !ets = withThisHostObj ets $
        \(Comput _thunk !appliedArgs effArgs !results) -> do
          let withEffsPart :: (Text -> STM ()) -> STM ()
              withEffsPart !exit' = case effArgs of
                [] -> exit' ""
                _ -> seqcontSTM (effRepr <$> effArgs) $ \ !effsRepr ->
                  exit' $ " {# " <> T.unwords effsRepr <> " #}"
              withResults :: (Text -> STM ()) -> STM ()
              withResults !exit' = case odToList results of
                [] -> exit' ""
                !kwargs ->
                  seqcontSTM (resultEntry <$> kwargs) $
                    exit' . ("{# " <>) . (<> " #}\n") . T.unwords
                where
                  resultEntry (k, v) !exit'' = edhValueRepr ets v $ \ !r ->
                    exit'' $ attrKeyStr k <> "= " <> r <> ","

          withEffsPart $ \ !effsPart ->
            withResults $ \ !resultsRepr -> case appliedArgs of
              [] ->
                exitEdh ets exit $
                  EdhString $ resultsRepr <> clsName <> "()" <> effsPart
              _ ->
                seqcontSTM (appliedRepr <$> appliedArgs) $ \ !argReprs ->
                  exitEdh ets exit $
                    EdhString $
                      resultsRepr
                        <> clsName
                        <> "( "
                        <> T.unwords argReprs
                        <> " )"
                        <> effsPart
        where
          appliedRepr ::
            (AppliedArg, Maybe (EdhValue, Dynamic)) ->
            (Text -> STM ()) ->
            STM ()
          appliedRepr (AppliedArg _anno !name _, Nothing) !exit' =
            exit' $ attrKeyStr name <> ","
          appliedRepr (AppliedArg _anno !name _, Just (v, _d)) !exit' =
            edhValueRepr ets v $ \ !vRepr ->
              exit' $ attrKeyStr name <> "= " <> vRepr <> ","

          effRepr ::
            (EffectfulArg, Maybe (EdhValue, Dynamic)) ->
            (Text -> STM ()) ->
            STM ()
          effRepr (EffectfulArg _anno !name _, Nothing) !exit' =
            exit' $ attrKeyStr name <> ","
          effRepr (EffectfulArg _anno !name _, Just (v, _d)) !exit' =
            edhValueRepr ets v $ \ !vRepr ->
              exit' $ attrKeyStr name <> "= " <> vRepr <> ","

      showProc :: ArgsPack -> EdhHostProc
      showProc _ !exit !ets = withThisHostObj ets $
        \(Comput !thunk !appliedArgs effArgs !results) -> do
          let withResults :: (Text -> STM ()) -> STM ()
              withResults !exit' = case odToList results of
                [] -> exit' ""
                !kwargs ->
                  seqcontSTM (resultEntry <$> kwargs) $
                    exit' . ("{# Results\n" <>) . (<> " #}\n") . T.unlines
                where
                  resultEntry (k, v) !exit'' = edhValueRepr ets v $ \ !r ->
                    exit'' $ "  " <> attrKeyStr k <> "= " <> r <> ","

          withResults $ \ !resultsLines ->
            seqcontSTM (appliedRepr <$> appliedArgs) $ \ !argReprs ->
              case thunk of
                Unapplied !unapplied ->
                  exitEdh ets exit $
                    EdhString $
                      resultsLines <> clsName <> "(\n" <> T.unlines argReprs
                        <> ") {# Unapplied "
                        <> T.pack (show unapplied)
                        <> " #}"
                Applied !applied ->
                  seqcontSTM (effRepr <$> effArgs) $ \ !effsRepr ->
                    exitEdh ets exit $
                      EdhString $
                        resultsLines <> clsName <> "(\n" <> T.unlines argReprs
                          <> ") {# Applied "
                          <> T.pack (show applied)
                          <> "\n"
                          <> T.unlines effsRepr
                          <> "#}"
                Effected !effected ->
                  seqcontSTM (effRepr <$> effArgs) $ \ !effsRepr ->
                    exitEdh ets exit $
                      EdhString $
                        resultsLines <> clsName <> "(\n" <> T.unlines argReprs
                          <> ") {# Effected "
                          <> T.pack (show effected)
                          <> "\n"
                          <> T.unlines effsRepr
                          <> "#}"
        where
          appliedRepr ::
            (AppliedArg, Maybe (EdhValue, Dynamic)) ->
            (Text -> STM ()) ->
            STM ()
          appliedRepr (AppliedArg !anno !name _, Nothing) !exit' =
            exit' $ "  " <> attrKeyStr name <> " :: " <> anno <> ","
          appliedRepr (AppliedArg !anno !name _, Just (v, _d)) !exit' =
            edhValueRepr ets v $ \ !vRepr ->
              exit' $
                "  " <> attrKeyStr name <> "= " <> vRepr <> " :: " <> anno
                  <> ","

          effRepr ::
            (EffectfulArg, Maybe (EdhValue, Dynamic)) ->
            (Text -> STM ()) ->
            STM ()
          effRepr (EffectfulArg !anno !name _, Nothing) !exit' =
            exit' $ "  " <> attrKeyStr name <> " :: " <> anno <> ","
          effRepr (EffectfulArg !anno !name _, Just (v, _d)) !exit' =
            edhValueRepr ets v $ \ !vRepr ->
              exit' $
                "  " <> attrKeyStr name <> "= " <> vRepr <> " :: " <> anno
                  <> ","

      callProc :: ArgsPack -> EdhHostProc
      callProc !apk !exit !ets = withThisHostObj ets $
        \ !comput -> applyComputArgs comput ets apk $ \ !comput' ->
          case comput'thunk comput' of
            Applied !applied -> do
              let !effArgs = comput'effectful'args comput'
              seqcontSTM (extractEffArg <$> effArgs) $
                \ !effs -> do
                  let effArgs' =
                        zipWith
                          ( \(!ea, _) !av ->
                              (ea, Just av)
                          )
                          effArgs
                          effs

                  case hostApply effs applied of
                    Nothing ->
                      throwEdh
                        ets
                        UsageError
                        "some effectful argument not applicable"
                    Just !applied' -> takeComputEffect applied' ets $ \case
                      Left (!effected, !results) -> do
                        !newOid <- unsafeIOToSTM newUnique
                        exitEdh ets exit $
                          EdhObject
                            this
                              { edh'obj'ident = newOid,
                                edh'obj'store =
                                  HostStore $
                                    toDyn
                                      comput'
                                        { comput'thunk = Effected effected,
                                          comput'effectful'args = effArgs',
                                          comput'results = results
                                        }
                              }
                      Right !result -> exitEdh ets exit result
            _ -> do
              !newOid <- unsafeIOToSTM newUnique
              exitEdh ets exit $
                EdhObject
                  this
                    { edh'obj'ident = newOid,
                      edh'obj'store = HostStore $ toDyn comput'
                    }
        where
          !ctx = edh'context ets
          !scope = contextScope ctx
          !this = edh'scope'this scope

          extractEffArg ::
            (EffectfulArg, Maybe (EdhValue, Dynamic)) ->
            ((EdhValue, Dynamic) -> STM ()) ->
            STM ()
          extractEffArg (_, Just !got) = ($ got)
          extractEffArg (EffectfulArg _anno _name !extractor, Nothing) =
            \ !exit' -> extractor ets $ \ !av !dd -> exit' (av, dd)

          hostApply :: [(EdhValue, Dynamic)] -> Dynamic -> Maybe Dynamic
          hostApply [] !df = Just df
          hostApply ((_v, a) : as) !df = dynApply df a >>= hostApply as
