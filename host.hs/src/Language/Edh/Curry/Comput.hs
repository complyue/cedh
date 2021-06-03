{-# LANGUAGE AllowAmbiguousTypes #-}

module Language.Edh.Curry.Comput where

import Control.Concurrent.STM
import Control.Monad
import Data.Dynamic
import qualified Data.Lossless.Decimal as D
import Data.Maybe
import Data.Text (Text)
import qualified Data.Text as T
import Data.Unique
import GHC.Conc (unsafeIOToSTM)
import Language.Edh.Curry.Shim
import Language.Edh.EHI
import Type.Reflection
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

-- * utility arg parsing helpers

appliedCountArg ::
  forall a.
  (Typeable a, Integral a) =>
  AttrKey ->
  AppliedArg
appliedCountArg = appliedCountArg' @a "positive!int!DecimalType"

appliedCountArg' ::
  forall a.
  (Typeable a, Integral a) =>
  AnnoText ->
  AttrKey ->
  AppliedArg
appliedCountArg' !anno !argName = AppliedArg anno argName $
  \ !ets !val !exit -> case edhUltimate val of
    EdhDecimal !d | d >= 1 -> case D.decimalToInteger d of
      Just !i -> exit val $ toDyn (fromInteger i :: a)
      Nothing -> edhValueDesc ets val $ \ !badDesc ->
        throwEdh ets UsageError $
          anno <> " as positive number expected but given: " <> badDesc
    _ -> edhValueDesc ets val $ \ !badDesc ->
      throwEdh ets UsageError $
        anno <> " as positive number expected but given: " <> badDesc

appliedIntArg :: forall a. (Typeable a, Integral a) => AttrKey -> AppliedArg
appliedIntArg = appliedIntArg' @a "int!DecimalType"

appliedIntArg' ::
  forall a.
  (Typeable a, Integral a) =>
  AnnoText ->
  AttrKey ->
  AppliedArg
appliedIntArg' !anno !argName = AppliedArg anno argName $
  \ !ets !val !exit -> case edhUltimate val of
    EdhDecimal !d -> case D.decimalToInteger d of
      Just !i -> exit val $ toDyn (fromInteger i :: a)
      Nothing -> edhValueDesc ets val $ \ !badDesc ->
        throwEdh ets UsageError $
          anno <> " as integer expected but given: " <> badDesc
    _ -> edhValueDesc ets val $ \ !badDesc ->
      throwEdh ets UsageError $
        anno <> " as integer expected but given: " <> badDesc

appliedFloatArg :: forall a. (Typeable a, RealFloat a) => AttrKey -> AppliedArg
appliedFloatArg = appliedFloatArg' @a "DecimalType"

appliedFloatArg' ::
  forall a.
  (Typeable a, RealFloat a) =>
  AnnoText ->
  AttrKey ->
  AppliedArg
appliedFloatArg' !anno !argName = AppliedArg anno argName $
  \ !ets !val !exit -> case edhUltimate val of
    EdhDecimal !d -> exit val $ toDyn $ D.decimalToRealFloat @a d
    _ -> edhValueDesc ets val $ \ !badDesc ->
      throwEdh ets UsageError $
        anno <> " as number expected but given: " <> badDesc

performFloatArg ::
  forall a.
  (Typeable a, RealFloat a) =>
  AttrKey ->
  EffectfulArg
performFloatArg !argName =
  performFloatArg' @a "DecimalType" argName $
    const $
      throwEdhTx UsageError $
        "missing effectful argument: " <> attrKeyStr argName

performFloatArg' ::
  forall a.
  (Typeable a, RealFloat a) =>
  AnnoText ->
  AttrKey ->
  (((EdhValue, a) -> EdhTx) -> EdhTx) ->
  EffectfulArg
performFloatArg' !anno !argName !effDefault =
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
                exit val $ toDyn (fromRational (toRational d) :: a)
              _ -> badArg

appliedHostSeqArg :: forall t. Typeable t => AttrKey -> AppliedArg
appliedHostSeqArg !argName = appliedHostSeqArg' @t typeName argName $
  \ !val !ds !exit -> exitEdhTx exit (val, toDyn $! snd <$> ds)
  where
    typeName = T.pack $ "[" <> show (typeRep @t) <> "]"

appliedHostSeqArg' ::
  forall t.
  Typeable t =>
  AnnoText ->
  AttrKey ->
  (EdhValue -> [(Object, t)] -> EdhTxExit (EdhValue, Dynamic) -> EdhTx) ->
  AppliedArg
appliedHostSeqArg' !typeName !argName !dmap = AppliedArg typeName argName $
  \ !ets !val !exit -> do
    let badArg = edhValueDesc ets val $ \ !badDesc ->
          throwEdh ets UsageError $
            "host objects " <> typeName <> " expected but given: " <> badDesc
        badArgElem elemVal = edhValueDesc ets elemVal $ \ !badDesc ->
          throwEdh ets UsageError $
            "host objects " <> typeName <> " expected but one is: " <> badDesc
        parseElements :: [(Object, t)] -> [EdhValue] -> STM ()
        parseElements results [] = runEdhTx ets $
          dmap val (reverse $! results) $ \(!val', !dd) _ets -> exit val' dd
        parseElements results (elemVal : rest) = case edhUltimate elemVal of
          EdhObject !obj -> case edh'obj'store obj of
            HostStore !dd -> case fromDynamic dd of
              Just !comput ->
                case comput'thunk comput of
                  Effected !effected -> case fromDynamic effected of
                    Just (d :: t) -> parseElements ((obj, d) : results) rest
                    Nothing -> badElem
                  Applied !applied | null (comput'effectful'args comput) ->
                    case fromDynamic applied of
                      Just (d :: t) -> parseElements ((obj, d) : results) rest
                      Nothing -> badElem
                  _ -> edhValueDesc ets val $ \ !badDesc ->
                    throwEdh ets UsageError $
                      "comput given for " <> attrKeyStr argName
                        <> " not effected, it is: "
                        <> badDesc
              Nothing -> case fromDynamic dd of
                Just (d :: t) -> parseElements ((obj, d) : results) rest
                Nothing -> badElem
            _ -> badElem
          _ -> badElem
          where
            badElem = badArgElem elemVal

    case edhUltimate val of
      EdhArgsPack (ArgsPack !args !kwargs)
        | odNull kwargs -> parseElements [] args
      EdhList (List _ !lv) -> readTVar lv >>= parseElements []
      _ -> badArg

appliedHostArg :: forall t. Typeable t => AttrKey -> AppliedArg
appliedHostArg !argName = appliedHostArg' @t typeName argName $
  \ !val _obj !d !exit -> exitEdhTx exit (val, toDyn d)
  where
    typeName = T.pack $ show (typeRep @t)

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
    typeName = T.pack $ show (typeRep @t)

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

-- * utilities providing argument default value, by constructing object of the

-- designated comput class

computArgDefault ::
  forall t. Typeable t => EdhValue -> (((EdhValue, t) -> EdhTx) -> EdhTx)
computArgDefault = computArgDefault' []

computArgDefault' ::
  forall t.
  Typeable t =>
  [EdhValue] ->
  EdhValue ->
  (((EdhValue, t) -> EdhTx) -> EdhTx)
computArgDefault' = flip computArgDefault'' []

computArgDefault'' ::
  forall t.
  Typeable t =>
  [EdhValue] ->
  [(AttrKey, EdhValue)] ->
  EdhValue ->
  (((EdhValue, t) -> EdhTx) -> EdhTx)
computArgDefault'' !args !kwargs !callee !exit =
  edhMakeCall callee (ArgsPack args $ odFromList kwargs) $ \ !val !ets -> do
    let badArg = edhValueDesc ets val $ \ !badDesc ->
          throwEdh ets UsageError $
            "bug: wrong host value constructed as default: " <> badDesc
    case edhUltimate val of
      EdhObject !obj -> case edh'obj'store obj of
        HostStore !dd -> case fromDynamic dd of
          Just !comput ->
            case comput'thunk comput of
              Effected !effected -> case fromDynamic effected of
                Just (d :: t) ->
                  runEdhTx ets $ exit (val, d)
                Nothing -> badArg
              Applied !applied | null (comput'effectful'args comput) ->
                case fromDynamic applied of
                  Just (d :: t) ->
                    runEdhTx ets $ exit (val, d)
                  Nothing -> badArg
              _ -> badArg
          Nothing -> case fromDynamic dd of
            Just (d :: t) ->
              runEdhTx ets $ exit (val, d)
            Nothing -> badArg
        _ -> badArg
      _ -> badArg

-- * Host representation of scriptable computations

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

computDone' :: Dynamic -> ComputTBP
computDone' = ComputDone

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
  { -- | Suggested constructor name
    comput'ctor'name :: !AttrName,
    -- | Thunk in possibly different stages
    comput'thunk :: !ComputThunk,
    -- | Formal arguments to be applied, with all or partial values collected
    comput'applied'args :: ![(AppliedArg, Maybe (EdhValue, Dynamic))],
    -- | Effectful arguments to be additionally applied per each call, with
    -- values collected in case of an effected computation.
    comput'effectful'args :: ![(EffectfulArg, Maybe (EdhValue, Dynamic))],
    -- | Results the computation actively yielded as it was effected
    comput'results :: KwArgs
  }

-- * Host computation manipulation utilities

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
  comput@(Comput !ctorName !thunk !appliedArgs !effectfulArgs !results)
  !ets
  apk@(ArgsPack !args !kwargs)
  !exit = case thunk of
    Unapplied !unapplied -> applyArgs appliedArgs $ \ !appliedArgs' ->
      allApplied [] appliedArgs' >>= \case
        Nothing ->
          exit $
            Comput ctorName thunk appliedArgs' effectfulArgs results
        Just !dds -> case hostApply 0 dds unapplied of
          Right !applied ->
            exit $
              Comput
                ctorName
                (Applied applied)
                appliedArgs'
                effectfulArgs
                results
          Left !nArgApplied ->
            seqcontSTM (appliedRepr <$> drop nArgApplied appliedArgs') $
              \ !appsRepr ->
                throwEdh ets UsageError $
                  "some computation argument not applicable:\n"
                    <> T.unlines appsRepr
    Applied {} ->
      if null args && odNull kwargs
        then exit comput
        else edhValueRepr ets (EdhArgsPack apk) $ \ !badRepr ->
          throwEdh ets UsageError $
            "extranenous args to applied comput result:" <> badRepr
    Effected {} ->
      throwEdh ets UsageError "you don't call already effected computation"
    where
      hostApply :: Int -> [Dynamic] -> Dynamic -> Either Int Dynamic
      hostApply _ [] !df = Right df
      hostApply !nArgApplied (a : as) !df = case dynApply df a of
        Nothing -> Left nArgApplied
        Just !appliedSoFar -> hostApply (nArgApplied + 1) as appliedSoFar

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

effectComput ::
  EdhThreadState ->
  Dynamic ->
  [(EffectfulArg, Maybe (EdhValue, Dynamic))] ->
  ( Either
      (Dynamic, [(EffectfulArg, Maybe (EdhValue, Dynamic))], KwArgs)
      EdhValue ->
    STM ()
  ) ->
  STM ()
effectComput !ets !applied !effArgs !exit =
  seqcontSTM (extractEffArg <$> effArgs) $
    \ !effs -> do
      let effArgs' =
            zipWith
              ( \(!ea, _) !av ->
                  (ea, Just av)
              )
              effArgs
              effs

      case hostApply 0 effs applied of
        Left !nArgApplied ->
          seqcontSTM (effRepr <$> drop nArgApplied effArgs) $ \ !effsRepr ->
            throwEdh
              ets
              UsageError
              $ "some effectful argument not applicable:\n"
                <> T.unlines effsRepr
        Right !applied' -> takeComputEffect applied' ets $ \case
          Left (!effected, !results) ->
            exit $ Left (effected, effArgs', results)
          Right !result -> exit $ Right result
  where
    extractEffArg ::
      (EffectfulArg, Maybe (EdhValue, Dynamic)) ->
      ((EdhValue, Dynamic) -> STM ()) ->
      STM ()
    extractEffArg (_, Just !got) = ($ got)
    extractEffArg (EffectfulArg _anno _name !extractor, Nothing) =
      \ !exit' -> extractor ets $ \ !av !dd -> exit' (av, dd)

    hostApply :: Int -> [(EdhValue, Dynamic)] -> Dynamic -> Either Int Dynamic
    hostApply _ [] !df = Right df
    hostApply !nArgApplied ((_v, a) : as) !df = case dynApply df a of
      Nothing -> Left nArgApplied
      Just !appliedSoFar -> hostApply (nArgApplied + 1) as appliedSoFar

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

-- * Host comput classes, definition & usage

-- | Obtain the 'Dynamic' value of a host object, it can be an effected comput
-- or a raw host value
effectedComput :: Object -> Maybe Dynamic
effectedComput !obj = case edh'obj'store obj of
  HostStore !dhs -> case fromDynamic dhs of
    Just comput@Comput {} -> case comput'thunk comput of
      Effected !effected -> Just effected
      _ -> Nothing
    _ -> Just dhs
  _ -> Nothing

createComputCtor ::
  Typeable t =>
  Object ->
  AttrName ->
  [AppliedArg] ->
  [EffectfulArg] ->
  t ->
  Scope ->
  STM EdhValue
createComputCtor = createComputCtor' True

createComputCtor' ::
  Typeable t =>
  Bool ->
  Object ->
  AttrName ->
  [AppliedArg] ->
  [EffectfulArg] ->
  t ->
  Scope ->
  STM EdhValue
-- todo make `constructor(computObj)` return the host ctor method
createComputCtor'
  !effOnCtor
  !clsComput
  !ctorName
  !ctorAppArgs
  !ctorEffArgs
  !hostComput
  !outerScope = do
    let !comput =
          Comput
            ctorName
            (Unapplied $ toDyn hostComput)
            ((,Nothing) <$> ctorAppArgs)
            ((,Nothing) <$> ctorEffArgs)
            odEmpty
    mkHostProc outerScope EdhMethod ctorName $
      (,WildReceiver) $
        \ !apk !exit !ets -> applyComputArgs comput ets apk $ \ !comput' ->
          case comput'thunk comput' of
            Applied !applied ->
              if effOnCtor
                then effectComput
                  ets
                  applied
                  (comput'effectful'args comput')
                  $ \case
                    Left (!effected, !effArgs, !results) ->
                      -- one-shot effection on construction
                      (exitEdh ets exit =<<) $
                        EdhObject
                          <$> edhCreateHostObj
                            clsComput
                            comput'
                              { comput'thunk = Effected effected,
                                comput'effectful'args = effArgs,
                                comput'results = results
                              }
                    Right !result -> exitEdh ets exit result
                else -- not to take effect on construction

                  (exitEdh ets exit =<<) $
                    EdhObject <$> edhCreateHostObj clsComput comput'
            _ ->
              -- leave it effected, or unapplied
              (exitEdh ets exit =<<) $
                EdhObject <$> edhCreateHostObj clsComput comput'

defineComputClass :: Scope -> STM Object
defineComputClass !clsOuterScope =
  mkHostClass clsOuterScope "Comput" computAllocator [] $
    \ !clsScope -> do
      !mths <-
        sequence $
          [ (AttrByName nm,) <$> mkHostProc clsScope vc nm hp
            | (nm, vc, hp) <-
                [ ("(@)", EdhMethod, wrapHostProc argReadProc),
                  ("([])", EdhMethod, wrapHostProc argReadProc),
                  ("__repr__", EdhMethod, (reprProc, PackReceiver [])),
                  ("__show__", EdhMethod, (showProc, PackReceiver [])),
                  ("__call__", EdhMethod, (callProc, WildReceiver))
                ]
          ]
      iopdUpdate mths $ edh'scope'entity clsScope
  where
    computAllocator :: ArgsPack -> EdhObjectAllocator
    computAllocator _apk _ctorExit !etsCtor =
      throwEdh etsCtor UsageError "Comput not constructable from Edh"

    -- Obtain an argument by name
    argReadProc :: EdhValue -> EdhHostProc
    argReadProc !keyVal !exit !ets = withThisHostObj ets $
      \(Comput _ctorName _thunk !appliedArgs effArgs !results) ->
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
      \(Comput !ctorName _thunk !appliedArgs effArgs !results) -> do
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
                EdhString $ resultsRepr <> ctorName <> "()" <> effsPart
            _ ->
              seqcontSTM (appliedRepr <$> appliedArgs) $ \ !argReprs ->
                exitEdh ets exit $
                  EdhString $
                    resultsRepr
                      <> ctorName
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
      \(Comput !ctorName !thunk !appliedArgs effArgs !results) -> do
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
                seqcontSTM (effRepr <$> effArgs) $ \ !effsRepr ->
                  exitEdh ets exit $
                    EdhString $
                      resultsLines <> ctorName <> "(\n" <> T.unlines argReprs
                        <> ") {# Unapplied "
                        <> T.pack (show unapplied)
                        <> "\n"
                        <> T.unlines effsRepr
                        <> "#}"
              Applied !applied ->
                seqcontSTM (effRepr <$> effArgs) $ \ !effsRepr ->
                  exitEdh ets exit $
                    EdhString $
                      resultsLines <> ctorName <> "(\n" <> T.unlines argReprs
                        <> ") {# Applied "
                        <> T.pack (show applied)
                        <> "\n"
                        <> T.unlines effsRepr
                        <> "#}"
              Effected !effected ->
                seqcontSTM (effRepr <$> effArgs) $ \ !effsRepr ->
                  exitEdh ets exit $
                    EdhString $
                      resultsLines <> ctorName <> "(\n" <> T.unlines argReprs
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
          Applied !applied ->
            effectComput ets applied (comput'effectful'args comput') $ \case
              Left (!effected, !effArgs, !results) -> do
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
                                  comput'effectful'args = effArgs,
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
