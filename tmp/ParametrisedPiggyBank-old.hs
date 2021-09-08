{-# LANGUAGE DataKinds                     #-}
{-# LANGUAGE FlexibleContexts              #-}
{-# LANGUAGE GeneralizedNewtypeDeriving    #-}
{-# LANGUAGE MultiParamTypeClasses         #-}
{-# LANGUAGE NoImplicitPrelude             #-}
{-# LANGUAGE OverloadedStrings             #-}
{-# LANGUAGE ScopedTypeVariables           #-}
{-# LANGUAGE TemplateHaskell               #-}
{-# LANGUAGE TypeApplications              #-}
{-# LANGUAGE TypeFamilies                  #-}
{-# LANGUAGE TypeOperators                 #-}
{-# OPTIONS_GHC -fno-warn-unused-imports   #-}
{-# OPTIONS_GHC -fno-warn-unused-top-binds #-}

module Plutus.Contracts.ParametrisedPiggyBank
(inValue,checkAmount,endpoints, ParametrisedPiggyBankSchema, MyRedeemer (..)) where

import           Control.Monad        hiding (fmap)
import           Data.Map             as Map hiding (empty)
import           Data.Text            (Text, unpack)
import           Data.Monoid          (Last (..))
import           Data.Void            (Void)
import           Plutus.Contract
import           PlutusTx             (toBuiltinData)
import qualified PlutusTx
import           PlutusTx.Prelude     hiding (Semigroup(..), unless)
import qualified PlutusTx.Prelude     as Plutus
import           Ledger               hiding (singleton)
import           Ledger.Constraints   as Constraints
import qualified Ledger.Typed.Scripts as Scripts
import           Ledger.Ada           as Ada
import           Playground.Contract
import           Playground.TH        (mkKnownCurrencies, mkSchemaDefinitions)
import           Playground.Types     (KnownCurrency (..))
import           Prelude              (IO, Semigroup (..), String)
import           Text.Printf          (printf)
import           Data.Text.Prettyprint.Doc.Extras (PrettyShow (..))
import           Prelude              (Semigroup (..), Show (..))
import           Plutus.Contract       as Contract
import           Plutus.V1.Ledger.Value (Value (..), assetClass, assetClassValueOf)
{-
data PPBParam = PPBParam
    { beneficiary :: PubKeyHash
    } deriving Show-}

newtype PPBParam = PPBParam PubKeyHash
    deriving (Show)

PlutusTx.makeLift ''PPBParam

newtype MyRedeemer = MyRedeemer Bool
    deriving (FromJSON, ToJSON, ToSchema)

PlutusTx.makeIsDataIndexed ''MyRedeemer [('MyRedeemer, 0)]

{-# INLINABLE mkValidator #-}
mkValidator :: PPBParam -> () -> MyRedeemer -> ScriptContext -> Bool
mkValidator _ (MyRedeemer isValid) ctx =
    isValid &&
    hasSufficientAmount &&
    signedByBeneficiary

    where
      contextInfo :: TxInfo
      contextInfo = scriptContextTxInfo ctx

      hasSufficientAmount :: Bool
      hasSufficientAmount =
          traceIfFalse "Sorry. Not enough lovelace" $ checkAmount $ inValue contextInfo

      signedByBeneficiary :: Bool
      signedByBeneficiary = traceIfFalse "Sorry. Not signed by beneficiary" txSignedBy contextInfo $ beneficiary p

{-# INLINABLE inValue #-}
inValue :: TxInfo -> Value
inValue ctx = valueSpent (scriptContextTxInfo ctx)

{-# INLINABLE checkAmount #-}
checkAmount :: Value -> Bool
checkAmount val = (assetClassValueOf val $ assetClass Ada.adaSymbol Ada.adaToken) > 1000000

data Typed
instance Scripts.ValidatorTypes Typed where
    type instance DatumType Typed    = ()
    type instance RedeemerType Typed = MyRedeemer

typedValidator :: PPBParam -> Scripts.TypedValidator Typed
typedValidator p = Scripts.mkTypedValidator @Typed
    ($$(PlutusTx.compile [|| mkValidator ||]) `PlutusTx.applyCode` PlutusTx.liftCode p)
    $$(PlutusTx.compile [|| wrap ||])
    where
        wrap = Scripts.wrapValidator @() @MyRedeemer

validator :: Validator
validator = Scripts.validatorScript typedValidator

valHash :: Ledger.ValidatorHash
valHash = Scripts.validatorHash typedValidator

scrAddress :: Ledger.Address
scrAddress = scriptAddress validator

data PutParams = PutParams
    { pbBeneficiary :: !PubKeyHash
    , amount      :: !Integer
    } deriving (Generic, ToJSON, FromJSON, ToSchema)

type ParametrisedPiggyBankSchema =
            Endpoint "put" PutParams
        .\/ Endpoint "empty" MyRedeemer
        .\/ Endpoint "inspect" MyRedeemer

put :: AsContractError e => PutParams -> Contract w s e ()
put pp = do
    utxos <- utxoAt scrAddress
    let totalVal = Plutus.foldMap (txOutValue . txOutTxOut) $ snd <$> Map.toList utxos
        numInputs = Map.size utxos
    logInfo @String $ "Putting to piggy bank currently holding "
            ++ show numInputs
            ++ " outputs with a total value of "
            ++ show totalVal
    let p  = PPBParam
                  {
                   beneficiary = pbBeneficiary pp
                  }
        tx = mustPayToTheScript () $ Ada.lovelaceValueOf $ amount pp
    ledgerTx <- submitTxConstraints (typedValidator p) tx
    void $ awaitTxConfirmed $ txId ledgerTx
    logInfo @String $ printf "Put %d lovelaces in the piggy bank" amount
             ++ "for beneficiary pk hash" ++ show $ beneficiary p

empty :: forall w s e. AsContractError e => MyRedeemer -> Contract w s e ()
empty r = do
    let p  = PPBParam
                     { beneficiary = pubKeyHash <$> ownPubKey
                     }
    utxos <- utxoAt $ scrAddress p
    let totalVal = Plutus.foldMap (txOutValue . txOutTxOut) $ snd <$> Map.toList utxos
        numInputs = Map.size utxos
    logInfo @String
        $ "Attempting to empty piggy bank currently holding "
            <> show numInputs
            <> " outputs with a total value of "
            <> show totalVal
    let
        orefs   = fst <$> Map.toList utxos
        lookups = Constraints.unspentOutputs utxos <>
                  Constraints.otherScript (validator p)
        tx :: TxConstraints Void Void
        tx      = mconcat [mustSpendScriptOutput oref $ Redeemer $ toBuiltinData r | oref <- orefs]
    ledgerTx <- submitTxConstraintsWith @Void lookups tx
    handleError (\err -> Contract.logInfo $ "caught error: " ++ unpack err) $ void $ awaitTxConfirmed $ txId ledgerTx
    logInfo @String $ "Emptied piggy bank."

inspect :: forall w s e. AsContractError e => MyRedeemer -> Contract w s e ()
inspect r = do
    let p  = PPBParam
                         { beneficiary = pubKeyHash <$> ownPubKey
                         }
    utxos <- utxoAt $ scrAddress p
    let totalVal = Plutus.foldMap (txOutValue . txOutTxOut) $ snd <$> Map.toList utxos
        numInputs = Map.size utxos
    logInfo @String
        $ "Inspeting utxos at script address"
            <> show numInputs
            <> " outputs with a total value of "
            <> show totalVal
            <> " with total Ada quantity of "
            <> show (assetClassValueOf totalVal $ assetClass Ada.adaSymbol Ada.adaToken)
    logInfo @String $ "Inspect complete"

put' :: Promise () ParametrisedPiggyBankSchema Text ()
put' = endpoint @"put" put

empty' :: Promise () ParametrisedPiggyBankSchema Text ()
empty' = endpoint @"empty" empty

inspect' :: Promise () ParametrisedPiggyBankSchema Text ()
inspect' = endpoint @"inspect" inspect

endpoints :: AsContractError e => Contract () ParametrisedPiggyBankSchema Text e
endpoints = do
    logInfo @String "Waiting for put or empty."
    selectList [put', empty', inspect'] >>  endpoints

-- these functions are used in the simulator
mkSchemaDefinitions ''ParametrisedPiggyBankSchema
mkKnownCurrencies []
