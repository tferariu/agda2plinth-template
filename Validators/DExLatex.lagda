\begin{code}[hide]
open import Haskell.Prelude
open import Lib
open import Value

module Validators.DExLatex where

-- Defining the types of our Plinth Datum, referred to as Label in Agda
\end{code}

\newcommand\dexLabel{%
\begin{code}
record Label : Set where
  no-eta-equality
  pattern
  field
    ratio  : Rational
    owner  : PubKeyHash
open Label public
\end{code}
}

\newcommand\dexInstance{%
\begin{code}
eqLabel : Label -> Label -> Bool
eqLabel b c = (ratio b == ratio c) &&
              (owner b == owner c)
instance
  iEqLabel : Eq Label
  iEqLabel ._==_ = eqLabel

{-# COMPILE AGDA2HS eqLabel #-}
{-# COMPILE AGDA2HS iEqLabel #-}
\end{code}
}


\newcommand\dexDatum{%
\begin{code}
Datum = (AssetClass × Label)
\end{code}
}

\begin{code}[hide]

{-# COMPILE AGDA2HS eqLabel #-}
{-# COMPILE AGDA2HS iEqLabel #-}
{-# COMPILE AGDA2HS Label #-}
{-# COMPILE AGDA2HS Datum #-}

-- The abstract ScriptContext
record ScriptContext : Set where
    field     
        inputVal      : Value
        outputVal     : Value
        outputDatum   : Datum
        payments      : List (PubKeyHash × Value)
        signature     : PubKeyHash
        continues     : Bool
        inputRef      : TxOutRef
        mint          : Integer
        tokCurrSymbol : CurrencySymbol
        validInterval : Interval

-- Functions equivalent to Plinth ScriptContext functions or provided by our template
--https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-ledger-api/PlutusLedgerApi-V3-Data-Contexts.html#t:ScriptContext

newDatum : ScriptContext -> Datum
newDatum ctx = ScriptContext.outputDatum ctx

oldValue : ScriptContext -> Value
oldValue ctx = ScriptContext.inputVal ctx

newValue : ScriptContext -> Value
newValue ctx = ScriptContext.outputVal ctx

continuing : ScriptContext -> Bool
continuing ctx = ScriptContext.continues ctx

getPayment' : PubKeyHash -> List (PubKeyHash × Value) -> Value
getPayment' pkh [] = emptyValue
getPayment' pkh ((pkh' , v) ∷ xs) =
  if pkh == pkh' then v else getPayment' pkh xs

getPayment : PubKeyHash -> ScriptContext -> Value
getPayment pkh ctx = getPayment' pkh (ScriptContext.payments ctx)

getMintedAmount : ScriptContext -> Integer
getMintedAmount ctx = ScriptContext.mint ctx 

ownCurrencySymbol : ScriptContext -> CurrencySymbol
ownCurrencySymbol = ScriptContext.tokCurrSymbol

ownAssetClass : TokenName -> ScriptContext -> AssetClass
ownAssetClass tn ctx = (ownCurrencySymbol ctx , tn)

checkTokenIn : AssetClass -> ScriptContext -> Bool
checkTokenIn ac ctx = assetClassValueOf (ScriptContext.inputVal ctx) ac == 1

checkTokenOut : AssetClass -> ScriptContext -> Bool
checkTokenOut ac ctx = assetClassValueOf (ScriptContext.outputVal ctx) ac == 1

checkSigned : PubKeyHash -> ScriptContext -> Bool
checkSigned sig ctx = sig == ScriptContext.signature ctx

checkTokenBurned : AssetClass -> ScriptContext -> Bool
checkTokenBurned tok ctx = ScriptContext.mint ctx == -1

consumes : TxOutRef -> ScriptContext -> Bool
consumes oref ctx = oref == ScriptContext.inputRef ctx

continuingAddr : Address -> ScriptContext -> Bool
continuingAddr addr ctx = ScriptContext.continues ctx

newDatumAddr : Address -> ScriptContext -> Datum
newDatumAddr adr ctx = newDatum ctx

newValueAddr : Address -> ScriptContext -> Value
newValueAddr adr ctx = newValue ctx

checkTokenOutAddr : Address -> AssetClass -> ScriptContext -> Bool
checkTokenOutAddr adr = checkTokenOut

checkPayment : PubKeyHash -> Value -> ScriptContext -> Bool
checkPayment pkh v ctx = getPayment pkh ctx == v

validRange : ScriptContext -> Interval
validRange ctx = ScriptContext.validInterval ctx

-- The type of the Plinth Redeemer
\end{code}

\newcommand\dexRedeemer{%
\begin{code}
data Redeemer : Set where
  Update   : Value -> Rational -> Redeemer
  Exchange : Integer -> PubKeyHash -> Redeemer
  Stop     : Redeemer
\end{code}
}

\newcommand\dexParams{%
\begin{code}
record Params : Set where
    no-eta-equality
    pattern
    field
      sellCurr  : AssetClass
      buyCurr  : AssetClass
open Params public
\end{code}
}

\begin{code}[hide]

{-# COMPILE AGDA2HS Redeemer #-}

-- The type of the smart contract parameters

{-# COMPILE AGDA2HS Params #-}

-- Helper functions of the validator
\end{code}

\newcommand\dexCheckRational{%
\begin{code}
checkRational : Rational -> Bool
checkRational r = (numerator r > 0) && (denominator r > 0)
\end{code}
}

\newcommand\dexRatioCompare{%
\begin{code}
ratioCompare : Integer -> Integer -> Rational -> Bool
ratioCompare amt pay r = amt * (numerator r) <= pay * (denominator r)
\end{code}
}

\newcommand\dexCheckPayment{%
\begin{code}
checkPaymentRatio : PubKeyHash -> Integer -> AssetClass
  -> Rational -> ScriptContext -> Bool
checkPaymentRatio pkh amt ac r ctx =
  ratioCompare amt (assetClassValueOf (getPayment pkh ctx) ac) r &&
  geq (getPayment pkh ctx) minValue
\end{code}
}

\begin{code}[hide]


{-# COMPILE AGDA2HS checkRational #-}
{-# COMPILE AGDA2HS ratioCompare #-}
{-# COMPILE AGDA2HS checkPaymentRatio #-}

-- The Validator
\end{code}

\newcommand\dexValidator{%
\begin{code}
agdaValidator : Params -> Datum -> Redeemer -> ScriptContext -> Bool
agdaValidator par (tok , lab) red ctx = checkTokenIn tok ctx &&
  (case red of λ where
    (Update v r) ->
      checkSigned (owner lab) ctx && checkRational r && geq v minValue &&
      newValue ctx == v && newDatum ctx == (tok , record {ratio = r ;
      owner = owner lab}) && continuing ctx && checkTokenOut tok ctx
    (Exchange amt pkh) ->
      newValue ctx + (assetClassValue (sellCurr par) amt) == oldValue ctx &&
      newDatum ctx == (tok , lab) && checkPaymentRatio (owner lab) amt
      (buyCurr par) (ratio lab) ctx && continuing ctx && checkTokenOut tok ctx
    Stop ->
      not (continuing ctx) && checkTokenBurned tok ctx &&
      checkSigned (owner lab) ctx )
\end{code}
}

\begin{code}[hide]



-- Helper functions of the Minting Policy Script
\end{code}

\newcommand\dexMintingChecks{%
\begin{code}
checkDatum : Address -> TokenName -> ScriptContext -> Bool
checkDatum addr tn ctx = case (newDatumAddr addr ctx) of λ where
  (tok , l) -> ownAssetClass tn ctx == tok && checkRational (ratio l)

checkValue : Address -> TokenName -> ScriptContext -> Bool
checkValue addr tn ctx = checkTokenOutAddr addr (ownAssetClass tn ctx) ctx
\end{code}
}

\newcommand\dexPolicy{%
\begin{code}
agdaPolicy : Params -> Address -> TxOutRef -> TokenName ->
  ⊤ -> ScriptContext -> Bool
agdaPolicy par addr oref tn _ ctx =
  if      amt == 1  then continuingAddr addr ctx &&
                         consumes oref ctx &&
                         checkDatum addr tn ctx &&
                         checkValue addr tn ctx 
  else if amt == -1 then not (continuingAddr addr ctx)
       else False
  where
    amt = getMintedAmount ctx
\end{code}
}
\begin{code}[hide]




-- The Thread Token Minting Policy


{-# COMPILE AGDA2HS agdaValidator #-}

{-# COMPILE AGDA2HS checkDatum #-}
{-# COMPILE AGDA2HS checkValue #-}
{-# COMPILE AGDA2HS agdaPolicy #-}





\end{code}
