\begin{code}[hide]

open import Haskell.Prelude hiding (lookup)
open import Lib
open import Value

module Validators.AccountSim where

-- Defining the types of our Plinth Datum, referred to as Label in Agda
\end{code}

\newcommand\accDat{%
\begin{code}
AccMap = List (PubKeyHash × Value)
Datum = (AssetClass × AccMap)
\end{code}
}

\newcommand\accSC{%
\begin{code}
record ScriptContext : Set where
    field     
        inputVal         : Value
        outputVal        : Value
        outputDatum      : Datum
        payments         : List (PubKeyHash × Value)
        signature        : PubKeyHash
        continues        : Bool
        inputRef         : TxOutRef
        mint             : Integer
        tokCurrSymbol    : CurrencySymbol
        validInterval    : Interval
\end{code}
}




\newcommand\accNewDatum{%
\begin{code}
newDatum : ScriptContext -> Datum
newDatum ctx = ScriptContext.outputDatum ctx
\end{code}
}


\newcommand\accOldValue{%
\begin{code}
oldValue : ScriptContext -> Value
oldValue ctx = ScriptContext.inputVal ctx
\end{code}
}

\newcommand\accNewValue{%
\begin{code}
newValue : ScriptContext -> Value
newValue ctx = ScriptContext.outputVal ctx
\end{code}
}

\newcommand\accContinuing{%
\begin{code}
continuing : ScriptContext -> Bool
continuing ctx = ScriptContext.continues ctx
\end{code}
}

\newcommand\accCheckTokOut{%
\begin{code}
checkTokenOut : AssetClass -> ScriptContext -> Bool
checkTokenOut ac ctx
  = assetClassValueOf (ScriptContext.outputVal ctx) ac == 1
\end{code}
}

\newcommand\accCheckTokOutAddr{%
\begin{code}
checkTokenOutAddr : Address -> AssetClass -> ScriptContext -> Bool
checkTokenOutAddr adr = checkTokenOut
\end{code}
}


\newcommand\accGetMintedAmt{%
\begin{code}
getMintedAmount : ScriptContext -> Integer
getMintedAmount ctx = ScriptContext.mint ctx 
\end{code}
}






\begin{code}[hide]
getPayment' : PubKeyHash -> List (PubKeyHash × Value) -> Value
getPayment' pkh [] = emptyValue
getPayment' pkh ((pkh' , v) ∷ xs)
  = if pkh == pkh' then v else getPayment' pkh xs

getPayment : PubKeyHash -> ScriptContext -> Value
getPayment pkh ctx = getPayment' pkh (ScriptContext.payments ctx)

ownCurrencySymbol : ScriptContext -> CurrencySymbol
ownCurrencySymbol = ScriptContext.tokCurrSymbol

ownAssetClass : TokenName -> ScriptContext -> AssetClass
ownAssetClass tn ctx = ((ScriptContext.tokCurrSymbol ctx) , tn)

checkTokenIn : AssetClass -> ScriptContext -> Bool
checkTokenIn ac ctx = assetClassValueOf (ScriptContext.inputVal ctx) ac == 1

        
checkSigned : PubKeyHash -> ScriptContext -> Bool
checkSigned sig ctx = ScriptContext.signature ctx == sig

checkTokenBurned : AssetClass -> ScriptContext -> Bool
checkTokenBurned tok ctx = ScriptContext.mint ctx == -1

consumes : TxOutRef -> ScriptContext -> Bool
consumes oref ctx = ScriptContext.inputRef ctx == oref

continuingAddr : Address -> ScriptContext -> Bool
continuingAddr addr ctx = ScriptContext.continues ctx

newDatumAddr : Address -> ScriptContext -> Datum
newDatumAddr adr ctx = newDatum ctx

newValueAddr : Address -> ScriptContext -> Value
newValueAddr adr ctx = newValue ctx



checkPayment : PubKeyHash -> Value -> ScriptContext -> Bool
checkPayment pkh v ctx = getPayment pkh ctx == v

validRange : ScriptContext -> Interval
validRange ctx = ScriptContext.validInterval ctx

-- The type of the Plinth Redeemer, referred to as Input in Agda
\end{code}

\newcommand\accRed{%
\begin{code}
data Redeemer : Set where
  Open      : PubKeyHash -> Redeemer
  Close     : PubKeyHash -> Redeemer
  Withdraw  : PubKeyHash -> Value -> Redeemer
  Deposit   : PubKeyHash -> Value -> Redeemer
  Transfer  : PubKeyHash -> PubKeyHash -> Value -> Redeemer
  Stop      : Redeemer
\end{code}
}


\newcommand\accInsert{%
\begin{code}
insert : PubKeyHash -> Value -> AccMap -> AccMap
insert pkh val [] = ((pkh , val) ∷ [])
insert pkh val ((x , y) ∷ xs) = if (pkh == x)
  then ((pkh , val) ∷ xs)
  else ((x , y) ∷ (insert pkh val xs))
\end{code}
}

\newcommand\accDelete{%
\begin{code}
delete : PubKeyHash -> AccMap -> AccMap
delete pkh [] = []
delete pkh ((x , y) ∷ xs) = if (pkh == x)
  then xs
  else ((x , y) ∷ (delete pkh xs))
\end{code}
}
  

\newcommand\accLookup{%
\begin{code}
lookup : PubKeyHash -> AccMap -> Maybe Value
lookup pkh [] = Nothing
lookup pkh ((x , y) ∷ xs) = if (pkh == x)
  then Just y
  else lookup pkh xs
\end{code}
}

\newcommand\accPragma{%
\begin{code}
{-# COMPILE AGDA2HS insert #-}
{-# COMPILE AGDA2HS delete #-}
{-# COMPILE AGDA2HS lookup #-}
{-# COMPILE AGDA2HS Redeemer #-}
\end{code}
}


\newcommand\accIsJust{%
\begin{code}
isJust : Maybe Value -> Bool
isJust Nothing = False
isJust (Just v) = True
\end{code}
}

\newcommand\accIsNothing{%
\begin{code}
isNothing : Maybe Value -> Bool
isNothing Nothing = True
isNothing (Just v) = False
\end{code}
}


\newcommand\accCheckEmpty{%
\begin{code}
checkEmpty : Maybe Value -> Bool
checkEmpty Nothing = False
checkEmpty (Just v) = v == emptyValue
\end{code}
}

\newcommand\accCheckWithdraw{%
\begin{code}
checkWithdraw : AssetClass -> Maybe Value -> PubKeyHash -> Value
                -> AccMap -> ScriptContext -> Bool
checkWithdraw tok Nothing _ _ _ _ = False
checkWithdraw tok (Just v) pkh val map ctx =
  geq val emptyValue && geq v val &&
  newDatum ctx == (tok , insert pkh (v - val) map)
\end{code}
}


\newcommand\accCheckDeposit{%
\begin{code}
checkDeposit : AssetClass -> Maybe Value -> PubKeyHash -> Value
               -> AccMap -> ScriptContext -> Bool
checkDeposit tok Nothing _ _ _ _ = False
checkDeposit tok (Just v) pkh val map ctx =
  geq val emptyValue &&
  newDatum ctx == (tok , insert pkh (v + val) map)
\end{code}
}

\newcommand\accCheckTransfer{%
\begin{code}
checkTransfer : AssetClass -> Maybe Value -> Maybe Value -> PubKeyHash
              -> PubKeyHash -> Value -> AccMap -> ScriptContext -> Bool
checkTransfer tok Nothing _ _ _ _ _ _ = False
checkTransfer tok (Just vF) Nothing _ _ _ _ _ = False
checkTransfer tok (Just vF) (Just vT) from to val map ctx =
  geq val emptyValue && geq vF val && from /= to &&
  newDatum ctx == (tok , insert from (vF - val) (insert to (vT + val) map))
\end{code}
}



\newcommand\accPragmaTwo{%
\begin{code}
{-# COMPILE AGDA2HS checkEmpty #-}
{-# COMPILE AGDA2HS checkWithdraw #-}
{-# COMPILE AGDA2HS checkDeposit #-}
{-# COMPILE AGDA2HS checkTransfer #-}
\end{code}
}




\newcommand\accVal{%
\begin{code}
agdaValidator : Datum -> Redeemer -> ScriptContext -> Bool
agdaValidator (tok , map) red ctx = checkTokenIn tok ctx &&
                                    (case red of λ where
\end{code}
}

\newcommand\accOpen{%
\begin{code}
    (Open pkh) -> checkTokenOut tok ctx && continuing ctx &&
                  checkSigned pkh ctx && isNothing (lookup pkh map) &&
                  newDatum ctx == (tok , insert pkh emptyValue map) &&
                  newValue ctx == oldValue ctx
\end{code}
}

\newcommand\accClose{%
\begin{code}
    (Close pkh) -> checkTokenOut tok ctx && continuing ctx &&
                   checkSigned pkh ctx && checkEmpty (lookup pkh map) &&
                   newDatum ctx == (tok , delete pkh map) &&
                   newValue ctx == oldValue ctx
\end{code}
}


\newcommand\accDeposit{%
\begin{code}
    (Deposit pkh val) -> checkTokenOut tok ctx && continuing ctx &&
                         checkSigned pkh ctx &&
                         checkDeposit tok (lookup pkh map) pkh val map ctx &&
                         newValue ctx == oldValue ctx + val
\end{code}
}

\newcommand\accWithdraw{%
\begin{code}
    (Withdraw pkh val) -> checkTokenOut tok ctx && continuing ctx &&
                          checkSigned pkh ctx &&
                          checkWithdraw tok (lookup pkh map) pkh val map ctx &&
                          newValue ctx == oldValue ctx - val
\end{code}
}

\newcommand\accTransfer{%
\begin{code}
    (Transfer from to val) ->
      checkTokenOut tok ctx && continuing ctx && checkSigned from ctx &&
      checkTransfer tok (lookup from map) (lookup to map) from to val map ctx &&
      newValue ctx == oldValue ctx 

\end{code}
}

\newcommand\accStop{%
\begin{code}
    Stop -> checkTokenBurned tok ctx && not (continuing ctx) && map == [] )
\end{code}
}




\newcommand\accCheckDatum{%
\begin{code}
checkDatum : Address -> TokenName -> ScriptContext -> Bool
checkDatum addr tn ctx = case (newDatumAddr addr ctx) of λ where
  (tok , map) -> ownAssetClass tn ctx == tok && map == []
\end{code}
}


\newcommand\accCheckValue{%
\begin{code}
checkValue : Address -> TokenName -> ScriptContext -> Bool
checkValue addr tn ctx = checkTokenOutAddr addr (ownAssetClass tn ctx) ctx &&
                         newValueAddr addr ctx == minValue +
                         assetClassValue (ownAssetClass tn ctx) 1
\end{code}
}


\newcommand\accPolicy{%
\begin{code}
agdaPolicy : Address -> TxOutRef -> TokenName -> ⊤ -> ScriptContext -> Bool
agdaPolicy addr oref tn _ ctx =
  if      amt == 1  then continuingAddr addr ctx && consumes oref ctx &&
                         checkDatum addr tn ctx && checkValue addr tn ctx
  else if amt == -1 then not (continuingAddr addr ctx)
       else False
  where
    amt = getMintedAmount ctx
\end{code}
}

\begin{code}[hide]
{-# COMPILE AGDA2HS agdaValidator #-}



{-# COMPILE AGDA2HS checkDatum #-}
{-# COMPILE AGDA2HS checkValue #-}

{-# COMPILE AGDA2HS agdaPolicy #-}


{-# COMPILE AGDA2HS AccMap #-}
{-# COMPILE AGDA2HS Datum #-}
\end{code}

\newcommand\accSkeleton{%
\begin{code}
agdaValidator' : Datum -> Redeemer -> ScriptContext -> Bool
agdaValidator' (tok , map) red ctx = checkTokenIn tok ctx &&
                                    (case red of λ where
    (Open pkh) -> True
    (Close pkh) -> True
    (Withdraw pkh val) -> True
    (Deposit pkh val) -> True
    (Transfer from to val) -> True
    Stop -> True )
\end{code}
}

