\begin{code}[hide]

open import Lib'
open import Haskell.Prelude hiding (lookup)
open import Relation.Binary.PropositionalEquality.Core

module Value' where

-- Defining an abstract Value, does not get exported since Value exists in Plinth
-- We cannot use the same definitions as Plinth because they are optimized for
-- Blockchain use and not amenable to proofs.
-- https://plutus.cardano.intersectmbo.org/haddock/latest/plutus-ledger-api/src/PlutusLedgerApi.V1.Value.html#Value

\end{code}


\newcommand\vDef{%
\begin{code}
Value = Map AssetClass Integer
\end{code}
}


\newcommand\vLookup{%
\begin{code}
lookupValue : AssetClass -> List (AssetClass × Integer) -> Integer
lookupValue ac [] = 0
lookupValue ac ((ac' , val') ∷ xs) =
  if ac == ac' then val'
               else lookupValue ac xs
\end{code}
}


\newcommand\vDelete{%
\begin{code}
deleteValue : AssetClass -> List (AssetClass × Integer) -> List (AssetClass × Integer) 
deleteValue ac [] = []
deleteValue ac ((ac' , val') ∷ xs) =
  if ac == ac' then xs
               else (ac' , val') ∷ (deleteValue ac xs)
\end{code}
}


\newcommand\vAdd{%
\begin{code}
addValueAux : List (AssetClass × Integer) -> List (AssetClass × Integer) -> List (AssetClass × Integer)
addValueAux [] [] = []
addValueAux [] (v ∷ vs) = v ∷ vs
addValueAux (v ∷ vs) [] = v ∷ vs
addValueAux v1@((ac , val) ∷ xs) v2@((ac' , val') ∷ ys)
  = (ac , val + (lookupValue ac v2)) ∷ addValueAux xs (deleteValue ac v2)

addValue : Value -> Value -> Value
addValue (MkMap v1) (MkMap v2) = MkMap (addValueAux v1 v2)
\end{code}
}

\newcommand\vSub{%
\begin{code}
negValue : Value -> Value
negValue (MkMap xs) = MkMap (map (λ (k , v) → (k , (negateInteger v))) xs)

subValue : Value -> Value -> Value
subValue v1 v2 = addValue v1 (negValue v2)
\end{code}
}

\newcommand\vEq{%
\begin{code}
eqValueAux : List (AssetClass × Integer) -> List (AssetClass × Integer) -> Bool
eqValueAux [] [] = True
eqValueAux [] (x ∷ xs) = if x .snd == 0 then eqValueAux [] xs else False
eqValueAux (x ∷ xs) [] = if x .snd == 0 then eqValueAux xs [] else False
eqValueAux v1@((ac , val) ∷ xs) v2@((ac' , val') ∷ ys)
  = if val == (lookupValue ac v2) then eqValueAux xs (deleteValue ac v2)
                                  else False

eqValue : Value -> Value -> Bool
eqValue (MkMap x) (MkMap y) = eqValueAux x y 
\end{code}
}



\newcommand\vLt{%
\begin{code}
ltValueAux : List (AssetClass × Integer) -> List (AssetClass × Integer) -> Bool
ltValueAux [] [] = False
ltValueAux [] (x ∷ xs) = if x .snd == 0 then ltValueAux [] xs else True
ltValueAux (x ∷ xs) [] = False 
ltValueAux v1@((ac , val) ∷ xs) v2@((ac' , val') ∷ ys)
  = if val < (lookupValue ac v2) then ltValueAux xs (deleteValue ac v2)
                                 else False

lt : Value -> Value -> Bool
lt (MkMap x) (MkMap y) = ltValueAux x y 
\end{code}
}

\newcommand\vOthers{%
\begin{code}
leq : Value -> Value -> Bool
leq v1 v2 = lt v1 v2 || eqValue v1 v2

gt : Value -> Value -> Bool
gt v1 v2 = lt v2 v1

geq : Value -> Value -> Bool
geq v1 v2 = leq v2 v1
\end{code}
}

\newcommand\vBuiltin{%
\begin{code}
emptyValue : Value
emptyValue = MkMap []

minValue : Value
minValue = MkMap ((ada , 3) ∷ [])

x2MinValue : Value
x2MinValue = MkMap ((ada , 6) ∷ [])

lovelaces : Value -> Integer
lovelaces (MkMap []) = 0
lovelaces (MkMap ((ac , amt) ∷ xs)) = if ac == ada then amt
                                         else lovelaces (MkMap xs)
\end{code}
}

\newcommand\vInstance{%
\begin{code}
instance
  iEqValue : Eq Value
  iEqValue ._==_ = eqValue

  iOrdFromLessThanValue : OrdFromLessThan Value
  iOrdFromLessThanValue .OrdFromLessThan._<_ = lt

  iOrdVal : Ord Value
  iOrdVal = record
    { OrdFromLessThan iOrdFromLessThanValue }

  iNumberValue : Number Value
  iNumberValue = record { Constraint = λ x → ⊤ ; fromNat = λ n → MkMap ((ada , (Integer.pos n)) ∷ []) }

  iNumValue : Num Value
  iNumValue .MinusOK _ _         = ⊤
  iNumValue .NegateOK _          = ⊤
  iNumValue .Num.FromIntegerOK _ = ⊤
  iNumValue ._+_ x y             = addValue x y 
  iNumValue ._-_ x y             = subValue x y 
  iNumValue ._*_ x y             = x 
  iNumValue .negate x            = negValue x 
  iNumValue .abs x               = x 
  iNumValue .signum x            = x 
  iNumValue .fromInteger n       = (MkMap ((ada , n) ∷ [])) 
\end{code}
}


\newcommand\vHelper{%
\begin{code}
assetClassValueOf : Value -> AssetClass -> Integer
assetClassValueOf (MkMap []) ac = 0
assetClassValueOf (MkMap ((ac' , amt) ∷ vs)) ac = if ac' == ac then amt else assetClassValueOf (MkMap vs) ac

assetClassValue : AssetClass -> Integer -> Value
assetClassValue ac amt = MkMap ((ac , amt) ∷ [])

checkMinValue : Value -> Bool
checkMinValue v = (assetClassValueOf v ada) >= 3
\end{code}
}


--Postulated properties of Value. 


\newcommand\vPostulate{%
\begin{code}
postulate
  commVal : ∀ (a b : Value) -> a + b ≡ b + a
  assocVal : ∀ (a b c : Value) -> (a + b) + c ≡ a + (b + c)
  v=v : ∀ (v : Value) -> (v == v) ≡ True
  ==vto≡ : ∀ (a b : Value) -> (a == b) ≡ True -> a ≡ b
  ≡vto== : ∀ (a b : Value) -> a ≡ b -> (a == b) ≡ True
  
  addValIdL : ∀ (a : Value) -> emptyValue + a ≡ a
  addValIdR : ∀ (a : Value) -> a + emptyValue ≡ a
  
  switchSides  : ∀ (a b c : Value) -> a - b ≡ c -> a ≡ c + b
  switchSides' : ∀ (a b c : Value) -> a + b ≡ c -> a ≡ c - b
  
  doubleNeg : ∀ (a : Value) -> a ≡ negValue (negValue a)

  v-v : ∀ (a : Value) -> subValue a a ≡ emptyValue

  geq-refl : ∀ (a : Value) -> geq a a ≡ True
  
  notGeqToLt : ∀ (a b : Value) -> geq a b ≡ False -> lt a b ≡ True
  ltToGt : ∀ (a b : Value) -> lt a b ≡ True -> gt b a ≡ True
  geqTrans : ∀ (a b c : Value) -> geq a b ≡ True -> geq b c ≡ True -> geq a c ≡ True

  sumLemma : ∀ (a b : Value)
           -> geq a emptyValue ≡ True
           -> geq b emptyValue ≡ True
           -> geq (addValue a b) emptyValue ≡ True

  diffLemma : ∀ (a b : Value)
            -> geq a b ≡ True
            -> geq (subValue a b) emptyValue ≡ True

  geqAddTrans : ∀ (a b c d : Value)
              -> geq a (addValue b c) ≡ True
              -> geq b d ≡ True
              -> geq a (addValue d c) ≡ True

  geqSub : ∀ (a b c : Value)
         -> geq a (addValue b c) ≡ True
         -> geq (subValue a b) c ≡ True
         
  lovelaceLemma : ∀ (a : Value) 
                        -> (lovelaces a >= lovelaces x2MinValue) ≡ True
                        -> geq a x2MinValue ≡ True
\end{code}
}

  
\begin{code}[hide]
switchSides'' : ∀ (a b c : Value) -> a + b ≡ c -> a ≡ c - b
switchSides'' a b c p rewrite doubleNeg b | sym p
  | (assocVal a (negValue (negValue b)) (negValue (negValue (negValue b))))
  | v-v (negValue (negValue b)) | addValIdR a = refl 

{-
sumLemma' : ∀ (a b : Value)
           -> geq a emptyValue ≡ True
           -> geq b emptyValue ≡ True
           -> geq (addValue a b) emptyValue ≡ True
sumLemma' (MkMap []) (MkMap []) = λ z z₁ → z
sumLemma' (MkMap []) (MkMap (x ∷ y)) = λ z z₁ → z₁ --λ z z₁ → z
sumLemma' (MkMap (x ∷ x₁)) (MkMap []) = λ z z₁ → z
sumLemma' (MkMap (x ∷ xs)) (MkMap (y ∷ ys)) p1 p2 with x .fst == y .fst in eq1
sumLemma' (MkMap (x ∷ xs)) (MkMap (y ∷ ys)) p1 p2 | True = {!!} --p1
sumLemma' (MkMap (x ∷ xs)) (MkMap (y ∷ ys)) p1 p2 | False with x .fst .fst < y .fst .fst in eq2
sumLemma' (MkMap (x ∷ xs)) (MkMap (y ∷ ys)) p1 p2 | False | True = {!!} --p1
sumLemma' (MkMap (x ∷ xs)) (MkMap (y ∷ ys)) p1 p2 | False | False with x .fst .fst == y .fst .fst in eq3
sumLemma' (MkMap (x ∷ xs)) (MkMap (y ∷ ys)) p1 p2 | False | False | True with x .fst .snd < y .fst .snd in eq4
sumLemma' (MkMap (x ∷ xs)) (MkMap (y ∷ ys)) p1 p2 | False | False | True | True = {!!} --p1
sumLemma' (MkMap (x ∷ xs)) (MkMap (y ∷ ys)) p1 p2 | False | False | True | False with x .fst .snd == y .fst .snd in eq5
sumLemma' (MkMap (x ∷ xs)) (MkMap (y ∷ ys)) p1 p2 | False | False | True | False | True = {!!} --p1
sumLemma' (MkMap (x ∷ xs)) (MkMap (y ∷ ys)) p1 p2 | False | False | True | False | False = {!!} --p1
sumLemma' (MkMap (x ∷ xs)) (MkMap (y ∷ ys)) p1 p2 | False | False | False  = {!!} --p1

diffLemma' : ∀ (a b : Value)
            -> geq a b ≡ True
            -> geq (subValue a b) emptyValue ≡ True
diffLemma' (MkMap []) (MkMap []) = λ z → z
diffLemma' (MkMap []) (MkMap (x ∷ y)) = λ ()
diffLemma' (MkMap (x ∷ x₁)) (MkMap []) = λ z → z
diffLemma' (MkMap (x ∷ xs)) (MkMap (y ∷ ys)) with x .fst .fst < y .fst .fst in eq1
diffLemma' (MkMap (x ∷ xs)) (MkMap (y ∷ ys)) | True = λ ()
diffLemma' (MkMap (x ∷ xs)) (MkMap (y ∷ ys)) | False with x .fst .fst == y .fst .fst in eq2
diffLemma' (MkMap (x ∷ xs)) (MkMap (y ∷ ys)) | False | True with x .fst .snd < y .fst .snd in eq3
diffLemma' (MkMap (x ∷ xs)) (MkMap (y ∷ ys)) | False | True | True = λ ()
diffLemma' (MkMap (x ∷ xs)) (MkMap (y ∷ ys)) | False | True | False with x .fst .snd == y .fst .snd in eq4
diffLemma' (MkMap (x ∷ xs)) (MkMap (y ∷ ys)) | False | True | False | True = λ z → {!!} --refl
diffLemma' (MkMap (x ∷ xs)) (MkMap (y ∷ ys)) | False | True | False | False = λ z → {!!} --z
diffLemma' (MkMap (x ∷ xs)) (MkMap (y ∷ ys)) | False | False = λ z → {!!} --z
-}

{-

  
  iSemigroupValue : Semigroup Value
  iSemigroupValue ._<>_ = addValue
  
  subLemma : ∀ (a b : Value)
           -> geq b emptyValue ≡ True
           -> geq a (subValue a b) ≡ True


  geqSum : ∀ (a b c : Value)
           -> geq a (addValue b c) ≡ True
           -> geq c emptyValue ≡ True
           -> geq a b ≡ True
  
         
 -- lovelaceLemma : ∀ (a b : Value) -> geq a b ≡ True -> (lovelaces a >= lovelaces b) ≡ True

 -- lovelaceSumLemma : ∀ (a b : Value) -> lovelaces (addValue a b) ≡ lovelaces a + lovelaces b
  
{-
lovelaceDiffLemma' : ∀ (a : Value) (i : Integer)
  -> lovelaces a ≡ i
  -> lovelaces (a - minValue) ≡ i - 3
lovelaceDiffLemma' (MkMap []) i refl = refl
lovelaceDiffLemma' (MkMap (x ∷ x₁)) i refl = {!!}
-}
  -}

\end{code}



