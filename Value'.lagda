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
lookupValue ac ((ac' , amt') ∷ xs) =
  if ac == ac' then amt'
               else lookupValue ac xs
\end{code}
}


\newcommand\vDelete{%
\begin{code}
deleteValue : AssetClass -> List (AssetClass × Integer)
           -> List (AssetClass × Integer) 
deleteValue ac [] = []
deleteValue ac ((ac' , amt') ∷ xs) =
  if ac == ac' then xs
               else (ac' , amt') ∷ (deleteValue ac xs)
\end{code}
}


\newcommand\vEq{%
\begin{code}
eqValueAux : List (AssetClass × Integer)
          -> List (AssetClass × Integer) -> Bool
eqValueAux [] [] = True
eqValueAux [] ((ac , amt) ∷ vs) = if amt == 0 then eqValueAux [] vs else False
eqValueAux ((ac , amt) ∷ vs) [] = if amt == 0 then eqValueAux vs [] else False
eqValueAux ((ac , amt) ∷ vs) v2@((ac' , amt') ∷ vs')
  = if amt == (lookupValue ac v2) then eqValueAux vs (deleteValue ac v2)
                                  else False

eqValue : Value -> Value -> Bool
eqValue (unMap x) (unMap y) = eqValueAux x y 
\end{code}
}


\newcommand\vAdd{%
\begin{code}
addValueAux : List (AssetClass × Integer)
           -> List (AssetClass × Integer) -> List (AssetClass × Integer)
addValueAux [] [] = []
addValueAux [] (v ∷ vs) = v ∷ vs
addValueAux (v ∷ vs) [] = v ∷ vs
addValueAux ((ac , amt) ∷ vs) v2@((ac' , amt') ∷ vs')
  = (ac , amt + (lookupValue ac v2)) ∷ addValueAux vs (deleteValue ac v2)

addValue : Value -> Value -> Value
addValue (unMap v1) (unMap v2) = unMap (addValueAux v1 v2)
\end{code}
}

\newcommand\vSub{%
\begin{code}
negValueAux : List (AssetClass × Integer) -> List (AssetClass × Integer)
negValueAux [] = []
negValueAux ((ac , amt) ∷ vs) = (ac , (negateInteger amt)) ∷ (negValueAux vs)

negValue : Value -> Value
negValue (unMap xs) = unMap (negValueAux xs)

subValue : Value -> Value -> Value
subValue v1 v2 = addValue v1 (negValue v2)
\end{code}
}



\newcommand\vLt{%
\begin{code}
ltValueAux : List (AssetClass × Integer)
          -> List (AssetClass × Integer) -> Bool
ltValueAux [] [] = False
ltValueAux [] ((ac , amt) ∷ vs) = if amt == 0 then ltValueAux [] vs else True
ltValueAux (v ∷ vs) [] = False 
ltValueAux ((ac , amt) ∷ vs) v2@((ac' , amt') ∷ vs')
  = if amt < (lookupValue ac v2) then ltValueAux vs (deleteValue ac v2)
                                 else False

lt : Value -> Value -> Bool
lt (unMap x) (unMap y) = ltValueAux x y 
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
emptyValue = unMap []

minValue : Value
minValue = unMap ((ada , 3) ∷ [])

x2MinValue : Value
x2MinValue = unMap ((ada , 6) ∷ [])
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
  iNumberValue = record { Constraint = λ x → ⊤ ; fromNat = λ n → unMap ((ada , (Integer.pos n)) ∷ []) }

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
  iNumValue .fromInteger n       = (unMap ((ada , n) ∷ [])) 
\end{code}
}

\newcommand\vLovelaces{%
\begin{code}                                       
lovelaces : Value -> Integer
lovelaces (unMap []) = 0
lovelaces (unMap ((ac , amt) ∷ vs)) = if ac == ada then amt
                                         else lovelaces (unMap vs)
\end{code}
}


                                         
\newcommand\vHelper{%
\begin{code}                                       
assetClassValueOf : Value -> AssetClass -> Integer
assetClassValueOf (unMap []) ac = 0
assetClassValueOf (unMap ((ac' , amt) ∷ vs)) ac =
  if ac' == ac then amt else assetClassValueOf (unMap vs) ac

assetClassValue : AssetClass -> Integer -> Value
assetClassValue ac amt = unMap ((ac , amt) ∷ [])
\end{code}
}



\newcommand\vPostulate{%
\begin{code}
postulate
  commVal : ∀ (a b : Value) -> a + b ≡ b + a
  assocVal : ∀ (a b c : Value) -> (a + b) + c ≡ a + (b + c)
  v=v : ∀ (a : Value) -> (a == a) ≡ True
  ==vto≡ : ∀ (a b : Value) -> (a == b) ≡ True -> a ≡ b
  ≡vto== : ∀ (a b : Value) -> a ≡ b -> (a == b) ≡ True
\end{code}
}


\newcommand\vSumLem{%
\begin{code}
  sumLemma : ∀ (a b : Value)
           -> geq a emptyValue ≡ True
           -> geq b emptyValue ≡ True
           -> geq (addValue a b) emptyValue ≡ True
\end{code}
}

\newcommand\vDiffLem{%
\begin{code}
  diffLemma : ∀ (a b : Value)
            -> geq a b ≡ True
            -> geq (subValue a b) emptyValue ≡ True
\end{code}
}



\newcommand\vValID{%
\begin{code}
  addValIdL : ∀ (a : Value) -> emptyValue + a ≡ a
  addValIdR : ∀ (a : Value) -> a + emptyValue ≡ a
\end{code}
}


\newcommand\vDN{%
\begin{code}
  v-v : ∀ (a : Value) -> subValue a a ≡ emptyValue
\end{code}
}



\newcommand\vGEQRefl{%
\begin{code}
  geq-refl : ∀ (a : Value) -> geq a a ≡ True
\end{code}
}



\begin{code}[hide] 

  doubleNeg : ∀ (a : Value) -> a ≡ negValue (negValue a)
  
  notGeqToLt : ∀ (a b : Value) -> geq a b ≡ False -> lt a b ≡ True
  ltToGt : ∀ (a b : Value) -> lt a b ≡ True -> gt b a ≡ True
  geqTrans : ∀ (a b c : Value) -> geq a b ≡ True -> geq b c ≡ True -> geq a c ≡ True

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


checkMinValue : Value -> Bool
checkMinValue v = (assetClassValueOf v ada) >= 3




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


\newcommand\vSSone{%
\begin{code}
switchSides : ∀ (a b c : Value) -> a - b ≡ c -> a ≡ c + b
switchSides a b c p rewrite sym p
  | assocVal a (negValue b) b | commVal (negValue b) b
  | v-v b | addValIdR a = refl
\end{code}
}

\newcommand\vSStwo{%
\begin{code}
switchSides' : ∀ (a b c : Value) -> a + b ≡ c -> a ≡ c - b
switchSides' a b c p rewrite sym p
  | assocVal a b (negValue b) | v-v b | addValIdR a = refl
\end{code}
}
