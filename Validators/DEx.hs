module Validators.DEx where

import Lib (Address, AssetClass, PubKeyHash, Rational, TokenName, TxOutRef, denominator, numerator)
import Value (Value, assetClassValue, assetClassValueOf, geq, minValue)

data Label = Label{ratio :: Rational, owner :: PubKeyHash}

type Datum = (AssetClass, Label)

data Redeemer = Update Value Rational
              | Exchange Integer PubKeyHash
              | Stop

data Params = Params{sellCurr :: AssetClass, buyCurr :: AssetClass}

checkRational :: Rational -> Bool
checkRational r = numerator r > 0 && denominator r > 0

ratioCompare :: Integer -> Integer -> Rational -> Bool
ratioCompare a b r = a * numerator r <= b * denominator r

checkPaymentRatio ::
                  PubKeyHash ->
                    Integer -> AssetClass -> Rational -> ScriptContext -> Bool
checkPaymentRatio pkh amt ac r ctx
  = ratioCompare amt (assetClassValueOf (getPayment pkh ctx) ac) r &&
      geq (getPayment pkh ctx) minValue

agdaValidator ::
              Params -> Datum -> Redeemer -> ScriptContext -> Bool
agdaValidator par (tok, lab) red ctx
  = checkTokenIn tok ctx &&
      case red of
          Update v r -> checkSigned (owner lab) ctx &&
                          checkRational r &&
                            geq v minValue &&
                              newValue ctx == v &&
                                newDatum ctx == (tok, Label r (owner lab)) &&
                                  continuing ctx && checkTokenOut tok ctx
          Exchange amt pkh -> newValue ctx +
                                assetClassValue (sellCurr par) amt
                                == oldValue ctx
                                &&
                                newDatum ctx == (tok, lab) &&
                                  checkPaymentRatio (owner lab) amt (buyCurr par) (ratio lab) ctx &&
                                    continuing ctx && checkTokenOut tok ctx
          Stop -> not (continuing ctx) &&
                    checkTokenBurned tok ctx && checkSigned (owner lab) ctx

checkDatum :: Address -> TokenName -> ScriptContext -> Bool
checkDatum addr tn ctx
  = case newDatumAddr addr ctx of
        (tok, l) -> ownAssetClass tn ctx == tok && checkRational (ratio l)

checkValue :: Address -> TokenName -> ScriptContext -> Bool
checkValue addr tn ctx
  = checkTokenOutAddr addr (ownAssetClass tn ctx) ctx

agdaPolicy ::
           Address -> TxOutRef -> TokenName -> () -> ScriptContext -> Bool
agdaPolicy addr oref tn _ ctx
  = if amt == 1 then
      continuingAddr addr ctx &&
        consumes oref ctx &&
          checkDatum addr tn ctx && checkValue addr tn ctx
      else if amt == (-1) then not (continuingAddr addr ctx) else False
  where
    amt :: Integer
    amt = getMintedAmount ctx

