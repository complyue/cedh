{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ImplicitParams #-}

module Language.Edh.Curry.Comput where

import Control.Concurrent.STM
import Control.Monad
import Data.Dynamic
import qualified Data.Lossless.Decimal as D
import Data.Maybe
import Data.Proxy (Proxy (..))
import Data.Text (Text)
import qualified Data.Text as T
import Data.Unique
import GHC.Conc (unsafeIOToSTM)
import GHC.TypeLits
import Language.Edh.Curry.Args
import Language.Edh.EHI
import Type.Reflection (typeRep)
import Prelude

-- | Scriptable Computation
class ScriptableComput c where
  scriptableArgs :: c -> [ScriptArgDecl]

  callByScript ::
    (?effecting :: Bool) =>
    c ->
    ArgsPack ->
    EdhTxExit ScriptedResult ->
    EdhTx

  argsScriptedAhead :: c -> KwArgs
  argsScriptedAhead _ = odEmpty

-- | Arg declaration, auto generated intermediate details, to provide meta
-- information to scripting environment
data ScriptArgDecl = ScriptArgDecl !IfEffectful !AttrKey !TypeName

type IfEffectful = Bool

type TypeName = Text

-- | Scripted Result
data ScriptedResult
  = -- | The computation done with a sole Edh value, though it can be a rather
    -- complex object on its own
    ScriptDone !EdhValue
  | -- | The computation done with a sole host value, and it intends to be
    -- recognizable by general Edh code, even not aware of 'ScriptedResult'
    ScriptDone' !Dynamic
  | -- | Partially applied host computation, with all args ever applied
    forall c.
    ScriptableComput c =>
    PartiallyApplied !c ![(ScriptArgDecl, EdhValue)]
  | -- | Fully applied host computation, with all args ever applied
    --
    -- It's pending effected yet, thus has to be called again with niladic apk
    -- to take effect. By "taking effect", it'll really resolve effectful
    -- arguments from that call site.
    forall c.
    ScriptableComput c =>
    FullyApplied !c ![(ScriptArgDecl, EdhValue)]
  | -- | The computation is finally done, with the result as a host value plus
    -- extra named result values, and with all args ever applied
    FullyEffected !Dynamic !KwArgs ![(ScriptArgDecl, EdhValue)]

-- | Argument Type that can be adapted from script values
class Typeable a => ScriptArgAdapter a where
  adaptedArgType :: Text
  adaptedArgType = T.pack $ show $ typeRep @a

  adaptEdhArg :: EdhValue -> EdhTxExit a -> EdhTx
  adaptedArgValue :: a -> EdhValue

-- | Scriptable Computation that waiting one more arg to be applied
--
-- this enables currying, by representing partially applied computation as
-- 1st class value
data PendingApplied name a v c
  = (KnownSymbol name, ScriptArgAdapter a, ScriptableComput c) =>
    PendingApplied !KwArgs !(ScriptArg a name -> c)

-- | apply one more arg to a previously saved, partially applied computation
instance
  (KnownSymbol name, ScriptArgAdapter a, ScriptableComput c) =>
  ScriptableComput (PendingApplied name a v c)
  where
  argsScriptedAhead (PendingApplied !pargs _f) = pargs

  scriptableArgs (PendingApplied _pargs !f) = scriptableArgs f

  callByScript (PendingApplied !pargs !f) (ArgsPack !args !kwargs) !exit =
    case odTakeOut argName kwargs of
      (Just !av, !kwargs') -> adaptEdhArg av $ \ !ad ->
        callByScript
          (f $ ScriptArg ad)
          (ArgsPack args $ odUnion pargs kwargs')
          $ \case
            ScriptDone !done -> exitEdhTx exit $ ScriptDone done
            ScriptDone' !done -> exitEdhTx exit $ ScriptDone' done
            PartiallyApplied c !appliedArgs ->
              exitEdhTx exit $
                PartiallyApplied c $
                  (argDecl, adaptedArgValue ad) : appliedArgs
            FullyApplied c !appliedArgs ->
              exitEdhTx exit $
                FullyApplied c $ (argDecl, adaptedArgValue ad) : appliedArgs
            FullyEffected d extras !appliedArgs ->
              exitEdhTx exit $
                FullyEffected d extras $
                  (argDecl, adaptedArgValue ad) : appliedArgs
      (Nothing, !kwargs') -> case args of
        av : args' -> adaptEdhArg av $ \ !ad ->
          callByScript
            (f $ ScriptArg ad)
            (ArgsPack args' $ odUnion pargs kwargs')
            $ \case
              ScriptDone !done -> exitEdhTx exit $ ScriptDone done
              ScriptDone' !done -> exitEdhTx exit $ ScriptDone' done
              PartiallyApplied c !appliedArgs ->
                exitEdhTx exit $
                  PartiallyApplied c $
                    (argDecl, adaptedArgValue ad) : appliedArgs
              FullyApplied c !appliedArgs ->
                exitEdhTx exit $
                  FullyApplied c $ (argDecl, adaptedArgValue ad) : appliedArgs
              FullyEffected d extras !appliedArgs ->
                exitEdhTx exit $
                  FullyEffected d extras $
                    (argDecl, adaptedArgValue ad) : appliedArgs
        [] ->
          exitEdhTx exit $ PartiallyApplied (PendingApplied kwargs' f) []
    where
      argName = AttrByName $ T.pack $ symbolVal (Proxy :: Proxy name)
      argDecl = ScriptArgDecl False argName (adaptedArgType @a)

-- | apply one more arg to a scriptable computation
instance
  {-# OVERLAPPABLE #-}
  (KnownSymbol name, ScriptArgAdapter a, ScriptableComput c) =>
  ScriptableComput (ScriptArg a name -> c)
  where
  scriptableArgs f =
    ScriptArgDecl False argName (adaptedArgType @a) :
    scriptableArgs (f undefined)
    where
      argName = AttrByName $ T.pack $ symbolVal (Proxy :: Proxy name)

  callByScript f (ArgsPack !args !kwargs) !exit =
    case odTakeOut argName kwargs of
      (Just !av, !kwargs') -> adaptEdhArg av $ \ !ad ->
        callByScript (f $ ScriptArg ad) (ArgsPack args kwargs') $ \case
          ScriptDone !done -> exitEdhTx exit $ ScriptDone done
          ScriptDone' !done -> exitEdhTx exit $ ScriptDone' done
          PartiallyApplied c !appliedArgs ->
            exitEdhTx exit $
              PartiallyApplied c $ (argDecl, adaptedArgValue ad) : appliedArgs
          FullyApplied c !appliedArgs ->
            exitEdhTx exit $
              FullyApplied c $ (argDecl, adaptedArgValue ad) : appliedArgs
          FullyEffected d extras !appliedArgs ->
            exitEdhTx exit $
              FullyEffected d extras $ (argDecl, adaptedArgValue ad) : appliedArgs
      (Nothing, !kwargs') -> case args of
        av : args' -> adaptEdhArg av $ \ !ad ->
          callByScript (f $ ScriptArg ad) (ArgsPack args' kwargs') $ \case
            ScriptDone !done -> exitEdhTx exit $ ScriptDone done
            ScriptDone' !done -> exitEdhTx exit $ ScriptDone' done
            PartiallyApplied c !appliedArgs ->
              exitEdhTx exit $
                PartiallyApplied c $ (argDecl, adaptedArgValue ad) : appliedArgs
            FullyApplied c !appliedArgs ->
              exitEdhTx exit $
                FullyApplied c $ (argDecl, adaptedArgValue ad) : appliedArgs
            FullyEffected d extras !appliedArgs ->
              exitEdhTx exit $
                FullyEffected d extras $ (argDecl, adaptedArgValue ad) : appliedArgs
        [] ->
          exitEdhTx exit $ PartiallyApplied (PendingApplied kwargs' f) []
    where
      argName = AttrByName $ T.pack $ symbolVal (Proxy :: Proxy name)
      argDecl = ScriptArgDecl False argName (adaptedArgType @a)

-- | Scriptable Computation that waiting to take effect
data PendingMaybeEffected name a c
  = (KnownSymbol name, ScriptArgAdapter a, ScriptableComput c) =>
    PendingMaybeEffected !(ScriptArg (Effective (Maybe a)) name -> c)

-- | resolve then apply one more effectful arg to previously saved, now
-- effecting computation
instance
  (KnownSymbol name, ScriptArgAdapter a, ScriptableComput c) =>
  ScriptableComput (PendingMaybeEffected name a c)
  where
  scriptableArgs (PendingMaybeEffected !f) = scriptableArgs f

  callByScript p@(PendingMaybeEffected !f) (ArgsPack !args !kwargs) !exit
    | not $ null args = throwEdhTx UsageError "extranous args"
    | not $ odNull kwargs = throwEdhTx UsageError "extranous kwargs"
    | not ?effecting = exitEdhTx exit $ FullyApplied p []
    | otherwise = applyMaybeEffectfulArg f exit

-- | resolve then apply one more effectful arg to the effecting computation
instance
  (KnownSymbol name, ScriptArgAdapter a, ScriptableComput c) =>
  ScriptableComput (ScriptArg (Effective (Maybe a)) name -> c)
  where
  scriptableArgs f =
    ScriptArgDecl True argName (T.pack (show $ typeRep @(Maybe a))) :
    scriptableArgs (f undefined)
    where
      argName = AttrByName $ T.pack $ symbolVal (Proxy :: Proxy name)

  callByScript !f (ArgsPack !args !kwargs) !exit
    | not $ null args = throwEdhTx UsageError "extranous args"
    | not $ odNull kwargs = throwEdhTx UsageError "extranous kwargs"
    | not ?effecting =
      exitEdhTx exit $ FullyApplied (PendingMaybeEffected f) []
    | otherwise = applyMaybeEffectfulArg f exit

-- | resolve then apply one more effectful arg to the effecting computation
applyMaybeEffectfulArg ::
  forall name a c.
  (KnownSymbol name, ScriptArgAdapter a, ScriptableComput c) =>
  (ScriptArg (Effective (Maybe a)) name -> c) ->
  EdhTxExit ScriptedResult ->
  EdhTx
applyMaybeEffectfulArg !f !exit = performEdhEffect' argName $ \ !maybeVal ->
  let ?effecting = True
   in case maybeVal of
        Nothing ->
          callByScript
            (f $ ScriptArg $ Effective Nothing)
            (ArgsPack [] odEmpty)
            $ \case
              ScriptDone !done -> exitEdhTx exit $ ScriptDone done
              FullyEffected d extras !appliedArgs ->
                exitEdhTx exit $ FullyEffected d extras appliedArgs
              _ -> error "bug: not fully effected"
        Just !av -> adaptEdhArg av $ \ !ad ->
          callByScript
            (f $ ScriptArg $ Effective $ Just ad)
            (ArgsPack [] odEmpty)
            $ \case
              ScriptDone !done -> exitEdhTx exit $ ScriptDone done
              FullyEffected d extras !appliedArgs ->
                exitEdhTx exit $
                  FullyEffected d extras $
                    (argDecl, adaptedArgValue ad) : appliedArgs
              _ -> error "bug: not fully effected"
  where
    argName = AttrByName $ T.pack $ symbolVal (Proxy :: Proxy name)
    argDecl = ScriptArgDecl True argName (T.pack $ show $ typeRep @(Maybe a))

-- | Scriptable Computation that waiting to take effect
data PendingEffected name a c
  = (KnownSymbol name, ScriptArgAdapter a, ScriptableComput c) =>
    PendingEffected !(ScriptArg (Effective a) name -> c)

-- | resolve then apply one more effectful arg to previously saved, now
-- effecting computation
instance
  (KnownSymbol name, ScriptArgAdapter a, ScriptableComput c) =>
  ScriptableComput (PendingEffected name a c)
  where
  scriptableArgs (PendingEffected !f) = scriptableArgs f

  callByScript p@(PendingEffected !f) (ArgsPack !args !kwargs) !exit
    | not $ null args = throwEdhTx UsageError "extranous args"
    | not $ odNull kwargs = throwEdhTx UsageError "extranous kwargs"
    | not ?effecting = exitEdhTx exit $ FullyApplied p []
    | otherwise = applyEffectfulArg f exit

-- | resolve then apply one more effectful arg to the effecting computation
instance
  {-# OVERLAPPABLE #-}
  (KnownSymbol name, ScriptArgAdapter a, ScriptableComput c) =>
  ScriptableComput (ScriptArg (Effective a) name -> c)
  where
  scriptableArgs f =
    ScriptArgDecl True argName (T.pack $ show $ typeRep @a) :
    scriptableArgs (f undefined)
    where
      argName = AttrByName $ T.pack $ symbolVal (Proxy :: Proxy name)

  callByScript !f (ArgsPack !args !kwargs) !exit
    | not $ null args = throwEdhTx UsageError "extranous args"
    | not $ odNull kwargs = throwEdhTx UsageError "extranous kwargs"
    | not ?effecting =
      exitEdhTx exit $ FullyApplied (PendingEffected f) []
    | otherwise = applyEffectfulArg f exit

-- | resolve then apply one more effectful arg to the effecting computation
applyEffectfulArg ::
  forall name a c.
  (KnownSymbol name, ScriptArgAdapter a, ScriptableComput c) =>
  (ScriptArg (Effective a) name -> c) ->
  EdhTxExit ScriptedResult ->
  EdhTx
applyEffectfulArg !f !exit = performEdhEffect' argName $ \ !maybeVal ->
  let ?effecting = True
   in case maybeVal of
        Nothing ->
          throwEdhTx UsageError $
            "missing effectful arg: " <> attrKeyStr argName
        Just !av -> adaptEdhArg av $ \ !ad ->
          callByScript
            (f $ ScriptArg $ Effective ad)
            (ArgsPack [] odEmpty)
            $ \case
              ScriptDone !done -> exitEdhTx exit $ ScriptDone done
              FullyEffected d extras !appliedArgs ->
                exitEdhTx exit $
                  FullyEffected d extras $
                    (argDecl, adaptedArgValue ad) : appliedArgs
              _ -> error "bug: not fully effected"
  where
    argName = AttrByName $ T.pack $ symbolVal (Proxy :: Proxy name)
    argDecl = ScriptArgDecl True argName (T.pack $ show $ typeRep @a)

-- * Computation result as base cases

-- | Wrap a pure computation result as scripted
data ComputDone a = (Typeable a) => ComputDone !a

instance ScriptableComput (ComputDone a) where
  scriptableArgs _ = []
  callByScript (ComputDone a) (ArgsPack !args !kwargs) !exit =
    if not (null args) || not (odNull kwargs)
      then throwEdhTx UsageError "extranous arguments"
      else exitEdhTx exit $ ScriptDone' (toDyn a)

-- | Wrap an Edh aware computation result as scripted
data ComputEdh a
  = Typeable a => ComputEdh (EdhThreadState -> (a -> STM ()) -> STM ())

instance ScriptableComput (ComputEdh a) where
  scriptableArgs _ = []

  callByScript (ComputEdh !act) (ArgsPack !args !kwargs) !exit !ets =
    if not (null args) || not (odNull kwargs)
      then throwEdh ets UsageError "extranous arguments"
      else act ets $ \ !a ->
        exitEdh ets exit $ ScriptDone' (toDyn a)

-- | Wrap an Edh aware computation result as scripted
--
-- Use this form in case you construct a 'Dynamic' result yourself
--
-- Note the type @a@ is for information purpose only, no way get asserted
newtype ComputEdh' a
  = ComputEdh' (EdhThreadState -> (Dynamic -> STM ()) -> STM ())

instance ScriptableComput (ComputEdh' a) where
  scriptableArgs _ = []

  callByScript (ComputEdh' !act) (ArgsPack !args !kwargs) !exit !ets =
    if not (null args) || not (odNull kwargs)
      then throwEdh ets UsageError "extranous arguments"
      else act ets $ \ !d -> exitEdh ets exit $ ScriptDone' d

-- | Wrap an Edh aware computation result as scripted
--
-- Use this form in case you can give out an 'EdhValue' directly
newtype ComputEdh''
  = ComputEdh'' (EdhThreadState -> (EdhValue -> STM ()) -> STM ())

instance ScriptableComput ComputEdh'' where
  scriptableArgs _ = []

  callByScript (ComputEdh'' !act) (ArgsPack !args !kwargs) !exit !ets =
    if not (null args) || not (odNull kwargs)
      then throwEdh ets UsageError "extranous arguments"
      else act ets $ \ !v -> exitEdh ets exit $ ScriptDone v

-- | Wrap an Edh aware computation result as scripted, and you would give out
-- one or more named results in addition, those can be separately obtained by
-- the script at will
data InflateEdh a
  = Typeable a =>
    InflateEdh (EdhThreadState -> (a -> KwArgs -> STM ()) -> STM ())

instance ScriptableComput (InflateEdh a) where
  scriptableArgs _ = []

  callByScript (InflateEdh !act) (ArgsPack !args !kwargs) !exit !ets =
    if not (null args) || not (odNull kwargs)
      then throwEdh ets UsageError "extranous arguments"
      else act ets $ \ !d !extras ->
        exitEdh ets exit $ FullyEffected (toDyn d) extras []

-- | Wrap an Edh aware computation result as scripted, and you would give out
-- one or more named results in addition, those can be separately obtained by
-- the script at will
--
-- Use this form in case you construct a 'Dynamic' result yourself
newtype InflateEdh' a
  = InflateEdh' (EdhThreadState -> (Dynamic -> KwArgs -> STM ()) -> STM ())

instance ScriptableComput (InflateEdh' a) where
  scriptableArgs _ = []

  callByScript (InflateEdh' !act) (ArgsPack !args !kwargs) !exit !ets =
    if not (null args) || not (odNull kwargs)
      then throwEdh ets UsageError "extranous arguments"
      else act ets $ \ !d !extras ->
        exitEdh ets exit $ FullyEffected d extras []

-- | Wrap a general effectful computation in the 'IO' monad
data ComputIO a = Typeable a => ComputIO (IO a)

instance ScriptableComput (ComputIO a) where
  scriptableArgs _ = []

  callByScript (ComputIO !act) (ArgsPack !args !kwargs) !exit !ets =
    if not (null args) || not (odNull kwargs)
      then throwEdh ets UsageError "extranous arguments"
      else runEdhTx ets $
        edhContIO $ do
          !d <- act
          atomically $ exitEdh ets exit $ ScriptDone' (toDyn d)

-- | Wrap a general effectful computation in the 'IO' monad
--
-- Use this form in case you construct a 'Dynamic' result yourself
--
-- Note the type @a@ is for information purpose only, no way get asserted
data ComputIO' a = Typeable a => ComputIO' (IO Dynamic)

instance ScriptableComput (ComputIO' a) where
  scriptableArgs _ = []

  callByScript (ComputIO' !act) (ArgsPack !args !kwargs) !exit !ets =
    if not (null args) || not (odNull kwargs)
      then throwEdh ets UsageError "extranous arguments"
      else runEdhTx ets $
        edhContIO $ do
          !d <- act
          atomically $ exitEdh ets exit $ ScriptDone' d

-- | Wrap a general effectful computation in the 'IO' monad
--
-- Use this form in case you can give out an 'EdhValue' directly
newtype ComputIO'' = ComputIO'' (IO EdhValue)

instance ScriptableComput ComputIO'' where
  scriptableArgs _ = []

  callByScript (ComputIO'' !act) (ArgsPack !args !kwargs) !exit !ets =
    if not (null args) || not (odNull kwargs)
      then throwEdh ets UsageError "extranous arguments"
      else runEdhTx ets $
        edhContIO $ do
          !v <- act
          atomically $ exitEdh ets exit $ ScriptDone v

-- | Wrap a general effectful computation in the 'STM' monad
data ComputSTM a = Typeable a => ComputSTM (STM a)

instance ScriptableComput (ComputSTM a) where
  scriptableArgs _ = []

  callByScript (ComputSTM !act) (ArgsPack !args !kwargs) !exit !ets =
    if not (null args) || not (odNull kwargs)
      then throwEdh ets UsageError "extranous arguments"
      else runEdhTx ets $
        edhContSTM $ do
          !d <- act
          exitEdh ets exit $ ScriptDone' (toDyn d)

-- | Wrap a general effectful computation in the 'STM' monad
--
-- Use this form in case you construct a 'Dynamic' result yourself
--
-- Note the type @a@ is for information purpose only, no way get asserted
newtype ComputSTM' a = ComputSTM' (STM Dynamic)

instance ScriptableComput (ComputSTM' a) where
  scriptableArgs _ = []

  callByScript (ComputSTM' !act) (ArgsPack !args !kwargs) !exit !ets =
    if not (null args) || not (odNull kwargs)
      then throwEdh ets UsageError "extranous arguments"
      else runEdhTx ets $
        edhContSTM $ do
          !d <- act
          exitEdh ets exit $ ScriptDone' d

-- | Wrap a general effectful computation in the 'STM' monad
--
-- Use this form in case you can give out an 'EdhValue' directly
newtype ComputSTM'' = ComputSTM'' (STM EdhValue)

instance ScriptableComput ComputSTM'' where
  scriptableArgs _ = []

  callByScript (ComputSTM'' !act) (ArgsPack !args !kwargs) !exit !ets =
    if not (null args) || not (odNull kwargs)
      then throwEdh ets UsageError "extranous arguments"
      else runEdhTx ets $
        edhContSTM $ do
          !v <- act
          exitEdh ets exit $ ScriptDone v

-- * Script Argument Adapters

instance ScriptArgAdapter EdhValue where
  adaptEdhArg !v !exit = exitEdhTx exit v
  adaptedArgValue = id

instance ScriptArgAdapter (Maybe Decimal) where
  adaptEdhArg !v !exit = case edhUltimate v of
    EdhNil -> exitEdhTx exit Nothing
    EdhDecimal !d -> exitEdhTx exit $ Just d
    _ -> badVal
    where
      badVal = edhValueDescTx v $ \ !badDesc ->
        throwEdhTx UsageError $
          "optional "
            <> adaptedArgType @Decimal
            <> " expected but given: "
            <> badDesc
  adaptedArgValue (Just !d) = EdhDecimal d
  adaptedArgValue Nothing = edhNothing

instance ScriptArgAdapter Decimal where
  adaptEdhArg !v !exit = case edhUltimate v of
    EdhDecimal !d -> exitEdhTx exit d
    _ -> badVal
    where
      badVal = edhValueDescTx v $ \ !badDesc ->
        throwEdhTx UsageError $
          adaptedArgType @Decimal <> " expected but given: " <> badDesc
  adaptedArgValue = EdhDecimal

instance ScriptArgAdapter (Maybe Double) where
  adaptEdhArg !v !exit = case edhUltimate v of
    EdhNil -> exitEdhTx exit Nothing
    EdhDecimal !d -> exitEdhTx exit $ Just $ D.decimalToRealFloat d
    _ -> badVal
    where
      badVal = edhValueDescTx v $ \ !badDesc ->
        throwEdhTx UsageError $
          "optional " <> adaptedArgType @Double
            <> " expected but given: "
            <> badDesc
  adaptedArgValue (Just !d) = EdhDecimal $ D.decimalFromRealFloat d
  adaptedArgValue Nothing = edhNothing

instance ScriptArgAdapter Double where
  adaptEdhArg !v !exit = case edhUltimate v of
    EdhDecimal !d -> exitEdhTx exit $ D.decimalToRealFloat d
    _ -> badVal
    where
      badVal = edhValueDescTx v $ \ !badDesc ->
        throwEdhTx UsageError $
          adaptedArgType @Double <> " expected but given: " <> badDesc
  adaptedArgValue = EdhDecimal . D.decimalFromRealFloat

instance ScriptArgAdapter (Maybe Integer) where
  adaptEdhArg !v !exit = case edhUltimate v of
    EdhNil -> exitEdhTx exit Nothing
    EdhDecimal !d -> case D.decimalToInteger d of
      Just !i -> exitEdhTx exit $ Just i
      Nothing -> badVal
    _ -> badVal
    where
      badVal = edhValueDescTx v $ \ !badDesc ->
        throwEdhTx UsageError $
          "optional " <> adaptedArgType @Integer
            <> " expected but given: "
            <> badDesc
  adaptedArgValue (Just !i) = EdhDecimal $ fromIntegral i
  adaptedArgValue Nothing = edhNothing

instance ScriptArgAdapter Integer where
  adaptEdhArg !v !exit = case edhUltimate v of
    EdhDecimal !d -> case D.decimalToInteger d of
      Just !i -> exitEdhTx exit i
      Nothing -> badVal
    _ -> badVal
    where
      badVal = edhValueDescTx v $ \ !badDesc ->
        throwEdhTx UsageError $
          adaptedArgType @Integer <> " expected but given: " <> badDesc
  adaptedArgValue !i = EdhDecimal $ fromIntegral i

instance ScriptArgAdapter (Maybe Int) where
  adaptEdhArg !v !exit = case edhUltimate v of
    EdhNil -> exitEdhTx exit Nothing
    EdhDecimal !d -> case D.decimalToInteger d of
      Just !i -> exitEdhTx exit $ Just $ fromInteger i
      Nothing -> badVal
    _ -> badVal
    where
      badVal = edhValueDescTx v $ \ !badDesc ->
        throwEdhTx UsageError $
          "optional " <> adaptedArgType @Int
            <> " expected but given: "
            <> badDesc
  adaptedArgValue (Just !i) = EdhDecimal $ fromIntegral i
  adaptedArgValue Nothing = edhNothing

instance ScriptArgAdapter Int where
  adaptEdhArg !v !exit = case edhUltimate v of
    EdhDecimal !d -> case D.decimalToInteger d of
      Just !i -> exitEdhTx exit $ fromInteger i
      Nothing -> badVal
    _ -> badVal
    where
      badVal = edhValueDescTx v $ \ !badDesc ->
        throwEdhTx UsageError $
          adaptedArgType @Int <> " expected but given: " <> badDesc
  adaptedArgValue !i = EdhDecimal $ fromIntegral i

newtype Count = Count Int

instance ScriptArgAdapter (Maybe Count) where
  adaptEdhArg !v !exit = case edhUltimate v of
    EdhNil -> exitEdhTx exit Nothing
    EdhDecimal !d | d >= 1 -> case D.decimalToInteger d of
      Just !i -> exitEdhTx exit $ Just $ Count $ fromInteger i
      Nothing -> badVal
    _ -> badVal
    where
      badVal = edhValueDescTx v $ \ !badDesc ->
        throwEdhTx UsageError $
          adaptedArgType @Count
            <> " (positive integer) expected but given: "
            <> badDesc
  adaptedArgValue (Just (Count !i)) = EdhDecimal $ fromIntegral i
  adaptedArgValue Nothing = edhNothing

instance ScriptArgAdapter Count where
  adaptEdhArg !v !exit = case edhUltimate v of
    EdhDecimal !d | d >= 1 -> case D.decimalToInteger d of
      Just !i -> exitEdhTx exit $ Count $ fromInteger i
      Nothing -> badVal
    _ -> badVal
    where
      badVal = edhValueDescTx v $ \ !badDesc ->
        throwEdhTx UsageError $
          adaptedArgType @Count
            <> " (positive integer) expected but given: "
            <> badDesc
  adaptedArgValue (Count !i) = EdhDecimal $ fromIntegral i

data HostSeq t = Typeable t => HostSeq ![t] ![Object]

instance Typeable t => ScriptArgAdapter (HostSeq t) where
  adaptedArgType = T.pack $ "[" <> show (typeRep @t) <> "]"

  adaptEdhArg !v !exit = case edhUltimate v of
    EdhArgsPack (ArgsPack !args !kwargs)
      | odNull kwargs -> exitWith args
    EdhList (List _u !lv) -> \ !ets ->
      readTVar lv >>= \ !vs -> runEdhTx ets $ exitWith vs
    _ -> badVal
    where
      badVal = edhValueDescTx v $ \ !badDesc ->
        throwEdhTx UsageError $
          adaptedArgType @(HostSeq t) <> " expected but given: " <> badDesc
      badElem ev = edhValueDescTx ev $ \ !badDesc ->
        throwEdhTx UsageError $
          T.pack (show $ typeRep @t)
            <> " element expected but given: "
            <> badDesc
      exitWith :: [EdhValue] -> EdhTx
      exitWith [] = exitEdhTx exit $ HostSeq [] []
      exitWith !vs = go vs []
        where
          go :: [EdhValue] -> [(t, Object)] -> EdhTx
          go [] rs = exitEdhTx exit $ uncurry HostSeq $ unzip $ reverse rs
          go (ev : rest) rs = case edhUltimate ev of
            EdhObject o -> case edh'obj'store o of
              HostStore dd -> case fromDynamic dd of
                Just (sr :: ScriptedResult) -> case sr of
                  FullyEffected d _extras _applied -> case fromDynamic d of
                    Just (t :: t) -> go rest ((t, o) : rs)
                    Nothing -> badElem ev
                  _ -> badElem ev
                Nothing -> case fromDynamic dd of
                  Just (t :: t) -> go rest ((t, o) : rs)
                  Nothing -> badElem ev
              _ -> badElem ev
            _ -> badElem ev

  adaptedArgValue (HostSeq _vals !objs) =
    EdhArgsPack $ ArgsPack (EdhObject <$> objs) odEmpty

data HostValue t = Typeable t => HostValue !t !Object

instance Typeable t => ScriptArgAdapter (Maybe (HostValue t)) where
  adaptedArgType = T.pack $ "Maybe " <> show (typeRep @t)

  adaptEdhArg !v !exit = case edhUltimate v of
    EdhNil -> exitEdhTx exit Nothing
    EdhObject o -> case edh'obj'store o of
      HostStore dd -> case fromDynamic dd of
        Just (sr :: ScriptedResult) -> case sr of
          FullyEffected d _extras _applied -> case fromDynamic d of
            Just (t :: t) -> exitEdhTx exit $ Just $ HostValue t o
            Nothing -> badVal
          _ -> badVal
        Nothing -> case fromDynamic dd of
          Just (t :: t) -> exitEdhTx exit $ Just $ HostValue t o
          Nothing -> badVal
      _ -> badVal
    _ -> badVal
    where
      badVal = edhValueDescTx v $ \ !badDesc ->
        throwEdhTx UsageError $
          adaptedArgType @(HostValue t) <> " expected but given: " <> badDesc

  adaptedArgValue (Just (HostValue _val !obj)) = EdhObject obj
  adaptedArgValue Nothing = edhNothing

instance Typeable t => ScriptArgAdapter (HostValue t) where
  adaptedArgType = T.pack $ show $ typeRep @t

  adaptEdhArg !v !exit = case edhUltimate v of
    EdhObject o -> case edh'obj'store o of
      HostStore dd -> case fromDynamic dd of
        Just (sr :: ScriptedResult) -> case sr of
          FullyEffected d _extras _applied -> case fromDynamic d of
            Just (t :: t) -> exitEdhTx exit $ HostValue t o
            Nothing -> badVal
          _ -> badVal
        Nothing -> case fromDynamic dd of
          Just (t :: t) -> exitEdhTx exit $ HostValue t o
          Nothing -> badVal
      _ -> badVal
    _ -> badVal
    where
      badVal = edhValueDescTx v $ \ !badDesc ->
        throwEdhTx UsageError $
          adaptedArgType @(HostValue t) <> " expected but given: " <> badDesc

  adaptedArgValue (HostValue _val !obj) = EdhObject obj

-- * Utilities

-- providing argument default value, by constructing object of the designated
-- comput class

appliedArgWithDefaultCtor ::
  forall t name.
  Typeable t =>
  EdhValue ->
  ScriptArg (Maybe (HostValue t)) name ->
  EdhTxExit t ->
  EdhTx
appliedArgWithDefaultCtor = appliedArgWithDefaultCtor' []

appliedArgWithDefaultCtor' ::
  forall t name.
  Typeable t =>
  [EdhValue] ->
  EdhValue ->
  ScriptArg (Maybe (HostValue t)) name ->
  EdhTxExit t ->
  EdhTx
appliedArgWithDefaultCtor' = flip appliedArgWithDefaultCtor'' []

appliedArgWithDefaultCtor'' ::
  forall t name.
  Typeable t =>
  [EdhValue] ->
  [(AttrKey, EdhValue)] ->
  EdhValue ->
  ScriptArg (Maybe (HostValue t)) name ->
  EdhTxExit t ->
  EdhTx
appliedArgWithDefaultCtor''
  !args
  !kwargs
  !callee
  (appliedArg -> !maybeHostVal)
  !exit = case maybeHostVal of
    Just (HostValue (t :: t) _obj) -> exitEdhTx exit t
    Nothing ->
      edhMakeCall' callee (ArgsPack args $ odFromList kwargs) $
        \ !val -> do
          let badArg = edhValueDescTx val $ \ !badDesc ->
                throwEdhTx UsageError $
                  "bug: wrong host value constructed as default for "
                    <> T.pack (show $ typeRep @t)
                    <> ": "
                    <> badDesc
          case edhUltimate val of
            EdhObject !o -> case edh'obj'store o of
              HostStore dd -> case fromDynamic dd of
                Just (sr :: ScriptedResult) -> case sr of
                  FullyEffected d _extras _applied -> case fromDynamic d of
                    Just (t :: t) -> exitEdhTx exit t
                    Nothing -> badArg
                  _ -> badArg
                Nothing -> case fromDynamic dd of
                  Just (t :: t) -> exitEdhTx exit t
                  Nothing -> badArg
              _ -> badArg
            _ -> badArg

effectfulArgWithDefaultCtor ::
  forall t name.
  Typeable t =>
  EdhValue ->
  ScriptArg (Effective (Maybe (HostValue t))) name ->
  EdhTxExit t ->
  EdhTx
effectfulArgWithDefaultCtor = effectfulArgWithDefaultCtor' []

effectfulArgWithDefaultCtor' ::
  forall t name.
  Typeable t =>
  [EdhValue] ->
  EdhValue ->
  ScriptArg (Effective (Maybe (HostValue t))) name ->
  EdhTxExit t ->
  EdhTx
effectfulArgWithDefaultCtor' = flip effectfulArgWithDefaultCtor'' []

effectfulArgWithDefaultCtor'' ::
  forall t name.
  Typeable t =>
  [EdhValue] ->
  [(AttrKey, EdhValue)] ->
  EdhValue ->
  ScriptArg (Effective (Maybe (HostValue t))) name ->
  EdhTxExit t ->
  EdhTx
effectfulArgWithDefaultCtor''
  !args
  !kwargs
  !callee
  (effectfulArg -> !maybeVal)
  !exit = case maybeVal of
    Just (HostValue (t :: t) _obj) -> exitEdhTx exit t
    Nothing ->
      edhMakeCall' callee (ArgsPack args $ odFromList kwargs) $
        \ !val -> do
          let badArg = edhValueDescTx val $ \ !badDesc ->
                throwEdhTx UsageError $
                  "bug: wrong host value constructed as default for "
                    <> T.pack (show $ typeRep @t)
                    <> ": "
                    <> badDesc
          case edhUltimate val of
            EdhObject !o -> case edh'obj'store o of
              HostStore dd -> case fromDynamic dd of
                Just (sr :: ScriptedResult) -> case sr of
                  FullyEffected d _extras _applied -> case fromDynamic d of
                    Just (t :: t) -> exitEdhTx exit t
                    Nothing -> badArg
                  _ -> badArg
                Nothing -> case fromDynamic dd of
                  Just (t :: t) -> exitEdhTx exit t
                  Nothing -> badArg
              _ -> badArg
            _ -> badArg

-- * Defining a Curried Host Computation class

type EffectOnCtor = Bool

appliedArgByKey :: AttrKey -> [(ScriptArgDecl, EdhValue)] -> EdhValue
appliedArgByKey k = go
  where
    go [] = nil
    go ((ScriptArgDecl _eff !ak _type, val) : rest)
      | ak == k = val
      | otherwise = go rest

defineComputMethod ::
  forall c.
  (Typeable c, ScriptableComput c) =>
  AttrName ->
  c ->
  Scope ->
  STM EdhValue
defineComputMethod !mthName !comput !outerScope =
  mkHostProc outerScope EdhMethod mthName (mthProc, argsRcvr)
  where
    mthProc :: ArgsPack -> EdhHostProc
    mthProc !apk !exit =
      let ?effecting = True
       in callByScript comput apk $ \ !sr !ets -> case sr of
            ScriptDone !done -> exitEdh ets exit done

    argsRcvr :: ArgsReceiver
    argsRcvr = NullaryReceiver -- TODO infer from scriptableArgs

defineComputClass ::
  forall c.
  (Typeable c, ScriptableComput c) =>
  AttrName ->
  c ->
  Scope ->
  STM Object
defineComputClass = defineComputClass' True

defineComputClass' ::
  forall c.
  (Typeable c, ScriptableComput c) =>
  EffectOnCtor ->
  AttrName ->
  c ->
  Scope ->
  STM Object
defineComputClass' !effOnCtor !clsName !rootComput !clsOuterScope =
  mkHostClass clsOuterScope clsName computAllocator [] $
    \ !clsScope -> do
      !mths <-
        sequence $
          [ (AttrByName nm,) <$> mkHostProc clsScope vc nm hp
            | (nm, vc, hp) <-
                [ ("(@)", EdhMethod, wrapHostProc attrReadProc),
                  ("([])", EdhMethod, wrapHostProc attrReadProc),
                  ("__repr__", EdhMethod, wrapHostProc reprProc),
                  ("__show__", EdhMethod, wrapHostProc showProc),
                  ("__call__", EdhMethod, wrapHostProc callProc)
                ]
          ]
      iopdUpdate mths $ edh'scope'entity clsScope
  where
    computAllocator :: ArgsPack -> EdhObjectAllocator
    computAllocator !apk !ctorExit !etsCtor =
      runEdhTx etsCtor $
        let ?effecting = effOnCtor
         in callByScript rootComput apk $ \ !sr _ets ->
              ctorExit Nothing $ HostStore $ toDyn sr

    -- Obtain an applied argument or a result field by name
    attrReadProc :: EdhValue -> EdhHostProc
    attrReadProc !keyVal !exit !ets = edhValueAsAttrKey ets keyVal $
      \ !argKey -> withThisHostObj' ets fromDynHostVal $ \case
        ScriptDone !done -> case argKey of
          AttrByName "self" -> exitEdh ets exit done
          _ -> exitEdh ets exit nil
        ScriptDone' {} -> case argKey of
          AttrByName "self" ->
            exitEdh ets exit $
              EdhObject $ edh'scope'that $ contextScope $ edh'context ets
          _ -> exitEdh ets exit nil
        PartiallyApplied _c appliedArgs ->
          exitEdh ets exit $ appliedArgByKey argKey appliedArgs
        FullyApplied _c appliedArgs ->
          exitEdh ets exit $ appliedArgByKey argKey appliedArgs
        FullyEffected _d !extras appliedArgs -> case odLookup argKey extras of
          Just !val -> exitEdh ets exit val
          Nothing -> exitEdh ets exit $ appliedArgByKey argKey appliedArgs
      where
        fromDynHostVal = case keyVal of
          EdhString "self" ->
            exitEdh ets exit $
              EdhObject $ edh'scope'that $ contextScope $ edh'context ets
          _ -> exitEdh ets exit nil

    reprProc :: ArgsPack -> EdhHostProc
    reprProc _ !exit !ets = withThisHostObj' ets fromDynHostVal $
      \case
        ScriptDone !done -> edhValueRepr ets done $ \ !doneRepr ->
          exitEdh ets exit $
            EdhString $ "{# " <> clsName <> " #} " <> doneRepr
        ScriptDone' !dd ->
          exitEdh ets exit $
            EdhString $ "{# " <> clsName <> ": " <> T.pack (show dd) <> " #} "
        PartiallyApplied c appliedArgs ->
          tshowAppliedArgs appliedArgs $ \ !appliedArgsRepr ->
            tshowArgsAhead (odToList $ argsScriptedAhead c) $
              \ !argsAheadRepr -> tshowMoreArgs (scriptableArgs c) $
                \ !moreArgsRepr ->
                  exitEdh ets exit $
                    EdhString $
                      clsName <> "( " <> appliedArgsRepr <> argsAheadRepr
                        <> ") {# "
                        <> moreArgsRepr
                        <> "#}"
        FullyApplied c appliedArgs ->
          tshowAppliedArgs appliedArgs $ \ !appliedArgsRepr ->
            tshowMoreArgs (scriptableArgs c) $ \ !moreArgsRepr ->
              exitEdh ets exit $
                EdhString $
                  clsName <> "( " <> appliedArgsRepr <> ") {# "
                    <> moreArgsRepr
                    <> "#}"
        FullyEffected _d extras appliedArgs ->
          tshowAppliedArgs appliedArgs $ \ !appliedArgsRepr ->
            tshowExtras (odToList extras) $
              \ !extrasRepr ->
                exitEdh ets exit $
                  EdhString $
                    clsName <> "( " <> appliedArgsRepr <> ") {# "
                      <> extrasRepr
                      <> "#}"
      where
        ctx = edh'context ets
        scope = contextScope ctx
        this = edh'scope'this scope

        tshowAppliedArgs ::
          [(ScriptArgDecl, EdhValue)] -> (Text -> STM ()) -> STM ()
        tshowAppliedArgs appliedArgs exit' = go appliedArgs exit'
          where
            go :: [(ScriptArgDecl, EdhValue)] -> (Text -> STM ()) -> STM ()
            go [] exit'' = exit'' ""
            go ((ScriptArgDecl !eff !k _type, !v) : rest) exit'' =
              go rest $ \ !restRepr -> edhValueRepr ets v $ \ !repr ->
                exit'' $
                  (if eff then "effect " else "")
                    <> attrKeyStr k
                    <> "= "
                    <> repr
                    <> ", "
                    <> restRepr

        tshowArgsAhead ::
          [(AttrKey, EdhValue)] -> (Text -> STM ()) -> STM ()
        tshowArgsAhead argsAhead exit' = go argsAhead exit'
          where
            go :: [(AttrKey, EdhValue)] -> (Text -> STM ()) -> STM ()
            go [] exit'' = exit'' ""
            go ((!k, !v) : rest) exit'' =
              go rest $ \ !restRepr -> edhValueRepr ets v $ \ !repr ->
                exit'' $
                  attrKeyStr k
                    <> "= "
                    <> repr
                    <> ", "
                    <> restRepr

        tshowMoreArgs :: [ScriptArgDecl] -> (Text -> STM ()) -> STM ()
        tshowMoreArgs moreArgs exit' = go moreArgs exit'
          where
            go :: [ScriptArgDecl] -> (Text -> STM ()) -> STM ()
            go [] exit'' = exit'' ""
            go (ScriptArgDecl !eff !k !typeName : rest) exit'' =
              go rest $ \ !restRepr ->
                exit'' $
                  (if eff then "effect " else "")
                    <> attrKeyStr k
                    <> " :: "
                    <> typeName
                    <> ", "
                    <> restRepr

        tshowExtras ::
          [(AttrKey, EdhValue)] -> (Text -> STM ()) -> STM ()
        tshowExtras es exit' = go es exit'
          where
            go :: [(AttrKey, EdhValue)] -> (Text -> STM ()) -> STM ()
            go [] exit'' = exit'' ""
            go ((!k, !v) : rest) exit'' =
              go rest $ \ !restRepr -> edhValueRepr ets v $ \ !repr ->
                exit'' $
                  attrKeyStr k
                    <> "= "
                    <> repr
                    <> ", "
                    <> restRepr

        fromDynHostVal = case edh'obj'store this of
          HostStore !dd ->
            exitEdh ets exit $
              EdhString $
                "{# " <> clsName <> ": <raw>" <> T.pack (show dd) <> " #} "
          _ -> throwEdh ets EvalError "bug: Comput not a host object"

    showProc :: ArgsPack -> EdhHostProc
    showProc _ !exit !ets = withThisHostObj' ets fromDynHostVal $
      \case
        ScriptDone !done -> edhValueRepr ets done $ \ !doneRepr ->
          exitEdh ets exit $
            EdhString $ clsName <> ": <done> " <> doneRepr
        ScriptDone' !dd ->
          exitEdh ets exit $
            EdhString $ clsName <> ": <host> " <> T.pack (show dd)
        PartiallyApplied c appliedArgs ->
          tshowAppliedArgs appliedArgs $ \ !appliedArgsRepr ->
            tshowArgsAhead (odToList $ argsScriptedAhead c) $
              \ !argsAheadRepr -> tshowMoreArgs (scriptableArgs c) $
                \ !moreArgsRepr ->
                  exitEdh ets exit $
                    EdhString $
                      clsName <> "(\n" <> appliedArgsRepr <> argsAheadRepr
                        <> "\n) {#\n"
                        <> moreArgsRepr
                        <> "\n#}"
        FullyApplied c appliedArgs ->
          tshowAppliedArgs appliedArgs $ \ !appliedArgsRepr ->
            tshowMoreArgs (scriptableArgs c) $ \ !moreArgsRepr ->
              exitEdh ets exit $
                EdhString $
                  clsName <> "(\n" <> appliedArgsRepr <> "\n) {#\n"
                    <> moreArgsRepr
                    <> "\n#}"
        FullyEffected _d extras appliedArgs ->
          tshowAppliedArgs appliedArgs $ \ !appliedArgsRepr ->
            tshowExtras (odToList extras) $
              \ !extrasRepr ->
                exitEdh ets exit $
                  EdhString $
                    clsName <> "(\n" <> appliedArgsRepr <> "\n) {#\n"
                      <> extrasRepr
                      <> "\n#}"
      where
        ctx = edh'context ets
        scope = contextScope ctx
        this = edh'scope'this scope

        tshowAppliedArgs ::
          [(ScriptArgDecl, EdhValue)] -> (Text -> STM ()) -> STM ()
        tshowAppliedArgs appliedArgs exit' = go appliedArgs exit'
          where
            go :: [(ScriptArgDecl, EdhValue)] -> (Text -> STM ()) -> STM ()
            go [] exit'' = exit'' ""
            go ((ScriptArgDecl !eff !k _type, !v) : rest) exit'' =
              go rest $ \ !restRepr -> edhValueRepr ets v $ \ !repr ->
                exit'' $
                  (if eff then "  effect " else "  ")
                    <> attrKeyStr k
                    <> "= "
                    <> repr
                    <> ",\n"
                    <> restRepr

        tshowArgsAhead ::
          [(AttrKey, EdhValue)] -> (Text -> STM ()) -> STM ()
        tshowArgsAhead argsAhead exit' = go argsAhead exit'
          where
            go :: [(AttrKey, EdhValue)] -> (Text -> STM ()) -> STM ()
            go [] exit'' = exit'' ""
            go ((!k, !v) : rest) exit'' =
              go rest $ \ !restRepr -> edhValueRepr ets v $ \ !repr ->
                exit'' $
                  "  "
                    <> attrKeyStr k
                    <> "= "
                    <> repr
                    <> ",\n"
                    <> restRepr

        tshowMoreArgs :: [ScriptArgDecl] -> (Text -> STM ()) -> STM ()
        tshowMoreArgs moreArgs exit' = go moreArgs exit'
          where
            go :: [ScriptArgDecl] -> (Text -> STM ()) -> STM ()
            go [] exit'' = exit'' ""
            go (ScriptArgDecl !eff !k !typeName : rest) exit'' =
              go rest $ \ !restRepr ->
                exit'' $
                  (if eff then "  effect " else "  ")
                    <> attrKeyStr k
                    <> " :: "
                    <> typeName
                    <> ",\n"
                    <> restRepr

        tshowExtras ::
          [(AttrKey, EdhValue)] -> (Text -> STM ()) -> STM ()
        tshowExtras es exit' = go es exit'
          where
            go :: [(AttrKey, EdhValue)] -> (Text -> STM ()) -> STM ()
            go [] exit'' = exit'' ""
            go ((!k, !v) : rest) exit'' =
              go rest $ \ !restRepr -> edhValueRepr ets v $ \ !repr ->
                exit'' $
                  "  "
                    <> attrKeyStr k
                    <> "= "
                    <> repr
                    <> ",\n"
                    <> restRepr

        fromDynHostVal = case edh'obj'store this of
          HostStore !dd ->
            exitEdh ets exit $
              EdhString $ clsName <> ": <raw> " <> T.pack (show dd)
          _ -> throwEdh ets EvalError "bug: Comput not a host object"

    callProc :: ArgsPack -> EdhHostProc
    callProc apk@(ArgsPack args kwargs) !exit !ets =
      withThisHostObj' ets fromDynHostVal $ \case
        ScriptDone !done ->
          if null args && odNull kwargs
            then exitEdh ets exit done
            else throwEdh ets UsageError "extranous arguments"
        ScriptDone' {} ->
          if null args && odNull kwargs
            then exitEdh ets exit $ EdhObject that
            else throwEdh ets UsageError "extranous arguments"
        PartiallyApplied c appliedArgs ->
          runEdhTx ets $
            let ?effecting = True
             in callByScript c apk $ exitWith appliedArgs
        FullyApplied c appliedArgs ->
          runEdhTx ets $
            let ?effecting = True
             in callByScript c apk $ exitWith appliedArgs
        FullyEffected {} ->
          if null args && odNull kwargs
            then exitEdh ets exit $ EdhObject that
            else throwEdh ets UsageError "extranous arguments"
      where
        ctx = edh'context ets
        scope = contextScope ctx
        this = edh'scope'this scope
        that = edh'scope'that scope

        fromDynHostVal =
          throwEdh ets UsageError "done computation not callable anymore"

        exitWith :: [(ScriptArgDecl, EdhValue)] -> ScriptedResult -> EdhTx
        exitWith appliedArgs sr _ets = case sr of
          ScriptDone !done -> exitEdh ets exit done
          ScriptDone' !dd -> exitDerived dd
          PartiallyApplied c' appliedArgs' ->
            exitDerived $
              toDyn $ PartiallyApplied c' $! appliedArgs ++ appliedArgs'
          FullyApplied c' appliedArgs' ->
            exitDerived $
              toDyn $ FullyApplied c' $! appliedArgs ++ appliedArgs'
          FullyEffected !d !extras appliedArgs' ->
            exitDerived $
              toDyn $ FullyEffected d extras $! appliedArgs ++ appliedArgs'
          where
            exitDerived :: Dynamic -> STM ()
            exitDerived dd = do
              !newOid <- unsafeIOToSTM newUnique
              exitEdh ets exit $
                EdhObject
                  this
                    { edh'obj'ident = newOid,
                      edh'obj'store = HostStore dd
                    }

-- | Obtain the 'Dynamic' value of a host object, it can be an effected comput
-- or a raw host value
effectedComput :: Object -> Maybe Dynamic
effectedComput !obj = case edh'obj'store obj of
  HostStore !dhs -> case fromDynamic dhs of
    Just (sr :: ScriptedResult) -> case sr of
      FullyEffected !d _extras _appliedArgs -> Just d
      ScriptDone' !d -> Just d
      _ -> Nothing
    _ -> Just dhs
  _ -> Nothing
