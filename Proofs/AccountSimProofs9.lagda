\begin{code}[hide]
open import Validators.AccountSim8
open import Lib'
open import Value'

open import Agda.Builtin.Char
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
import Data.Nat as N
open import Data.Integer hiding (_+_; _-_)
open import Data.Integer.Properties
open import Agda.Builtin.Int
open import Agda.Builtin.Nat renaming (_==_ to eqNat; _<_ to ltNat; _+_ to addNat; _-_ to monusNat; _*_ to mulNat)
open import Data.List hiding (lookup)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.Core
open import Data.Empty
open import Data.Sum.Base
open import Data.Product using (∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩; _×_ to _xx_)
open import Haskell.Prim hiding (⊥) 
open import Haskell.Prim.Integer
open import Haskell.Prim.Bool
open import Haskell.Prim.Eq
open import Haskell.Prim.Ord
open import Haskell.Prim.Maybe
open import Haskell.Prim.Tuple
open import Haskell.Prim.Ord using (_<=_ ; _>=_)
open import Haskell.Prim using (lengthNat)
open import Haskell.Prelude using (_+_ ; _-_)
open import Function.Base using (_∋_)
open _×_×_

open import ProofLib'

module Proofs.AccountSimProofs9 where

-- Model and proofs for the Account Simulation contract
  
-- The States of the State Transition System

\end{code}

\newcommand\mState{%
\begin{code}
record State : Set where
  field
    datum       : Datum
    value       : Value  
    tsig        : PubKeyHash
    spends      : TxOutRef
    threadTokCS : CurrencySymbol
open State
\end{code}
}

\begin{code}[hide]


-- Model parameters consisting of the combined parameters of the validator and minting policy
\end{code}

\newcommand\mParams{%
\begin{code}
record MParams : Set where
    field
        uniqueId      : TxOutRef
        threadTokName : TokenName
open MParams public
\end{code}
}

\begin{code}[hide]
--Transition Rules
--The Initial Transition

\end{code}

\newcommand\mInitial{%
\begin{code}
data _⊢_ : MParams -> State -> Set
  where
  TStart : ∀ {par s}
    -> datum s ≡ ((threadTokCS s , threadTokName par) , [] )
    -> spends s ≡ uniqueId par 
    -> value s ≡ minValue + assetClassValue
                (threadTokCS s , threadTokName par) 1
    -------------------
    -> par ⊢ s
\end{code}
}

\begin{code}[hide]


-- The Running Transition

\end{code}

\newcommand\mOpen{%
\begin{code}
data _⊢_~[_]~>_ : MParams -> State -> Redeemer -> State -> Set
  where
  TOpen : ∀ {par pkh s s' tok map}
    -> datum s ≡ (tok , map)
    -> tsig s' ≡ pkh 
    -> lookup pkh map ≡ Nothing
    -> datum s' ≡ (tok , insert pkh emptyValue map)
    -> value s' ≡ value s 
    -------------------
    -> par ⊢ s ~[ (Open pkh) ]~> s'
\end{code}
}

\newcommand\mClose{%
\begin{code}
  TClose : ∀ {par pkh s s' tok map}
    -> datum s ≡ (tok , map)
    -> tsig s' ≡ pkh
    -> lookup pkh map ≡ Just emptyValue
    -> datum s' ≡ (tok , delete pkh map)
    -> value s' ≡ value s
    -------------------
    -> par ⊢ s ~[ (Close pkh) ]~> s'
\end{code}
}


\newcommand\mDeposit{%
\begin{code}
  TDeposit : ∀ {par pkh val s s' v tok map}
    -> datum s ≡ (tok , map)
    -> tsig s' ≡ pkh
    -> lookup pkh map ≡ Just v
    -> geq val emptyValue ≡ true
    -> datum s' ≡ (tok , (insert pkh (v + val) map))
    -> value s' ≡ (value s) + val
    -------------------
    -> par ⊢  s ~[ (Deposit pkh val) ]~> s'
\end{code}
}

\newcommand\mWithdraw{%
\begin{code}
  TWithdraw : ∀ {par pkh val s s' v tok map}
    -> datum s ≡ (tok , map)
    -> tsig s' ≡ pkh
    -> lookup pkh map ≡ Just v
    -> geq val emptyValue ≡ true
    -> geq v val ≡ true
    -> datum s' ≡ (tok , (insert pkh (v - val) map))
    -> value s' ≡ (value s) - val 
    -------------------
    -> par ⊢ s ~[ (Withdraw pkh val) ]~> s'
\end{code}
}
    
 \newcommand\mTransfer{%
\begin{code}
  TTransfer : ∀ {par from to val s s' vF vT tok map}
    -> datum s ≡ (tok , map)
    -> tsig s' ≡ from
    -> lookup from map ≡ Just vF
    -> lookup to map ≡ Just vT
    -> geq val emptyValue ≡ true
    -> geq vF val ≡ true
    -> from ≢ to
    -> datum s' ≡ (tok , (insert from (vF - val)
                         (insert to (vT + val) map)))
    -> value s' ≡ value s
    -------------------
    -> par ⊢ s ~[ (Transfer from to val) ]~> s'

\end{code}
}

\newcommand\mFinal{%
\begin{code}
data _⊢_~[_]~|_ : MParams -> State -> Redeemer -> State -> Set
  where
  TStop : ∀ {par s s'}
    -> snd (datum s) ≡ []
    -------------------
    -> par ⊢ s ~[ Stop ]~| s'
\end{code}
}


\begin{code}[hide]




--Multi-Step Transition
\end{code}

\newcommand\mMulti{%
\begin{code}
data _⊢_~[_]~*_ : MParams -> State -> List Redeemer -> State -> Set
  where
  nil : ∀ { par s }
    ----------------------
    -> par ⊢ s ~[ [] ]~* s

  cons : ∀ { par s s' s'' i is }
    -> par ⊢ s ~[ i ]~> s'
    -> par ⊢ s' ~[ is ]~* s''
    -------------------------
    -> par ⊢ s ~[ (i ∷ is) ]~* s''
\end{code}
}

\begin{code}[hide]
--Transition Rules


\end{code}

\newcommand\mMultiF{%
\begin{code}
data _⊢_~[_]~|*_ : MParams -> State -> List Redeemer -> State -> Set
  where
  fin : ∀ { par s s' s'' is i }
    -> par ⊢ s ~[ is ]~* s'
    -> par ⊢ s' ~[ i ]~| s''
    ---------------------------------
    -> par ⊢ s ~[ (is ++ [ i ]) ]~|* s''
\end{code}
}

\begin{code}[hide]





-- Extra definitions necessary for the model


\end{code}

\newcommand\mHelper{%
\begin{code}
threadToken : State -> AssetClass
threadToken s = s .datum .fst

accMap : State -> AccMap
accMap s = s .datum .snd
\end{code}
}

\begin{code}[hide]


-- Validity predicate
\end{code}

\newcommand\mValid{%
\begin{code}
valid : State -> Set 
valid s = All (\y -> geq (snd y) emptyValue ≡ true) (accMap s)
\end{code}
}

\begin{code}[hide]

-- Lemmas for Validity

\end{code}

\newcommand\mLem{%
\begin{code}
lem : ∀ {pkh} (map : AccMap) (v : Value)
      -> geq v emptyValue ≡ true 
      -> All (λ y → geq (snd y) emptyValue ≡ true) map
      -> All (λ y → geq (snd y) emptyValue ≡ true) (insert pkh v map)
\end{code}
}

\newcommand\mLemP{%
\begin{code}
lem {pkh} [] v' p1 p2 = allCons {{p1}}
lem {pkh} ((pkh' , v) ∷ map) v' p1 (allCons {{i}} {{is}}) with pkh == pkh'
...| true = allCons {{p1}}
...| false = allCons {{i}} {{lem map v' p1 is}}
\end{code}
}

\newcommand\mDelem{%
\begin{code}
delem : ∀ {pkh} (map : AccMap)
      -> All (λ y → geq (snd y) emptyValue ≡ true) map
      -> All (λ y → geq (snd y) emptyValue ≡ true) (delete pkh map)
\end{code}
}

\newcommand\mDelemP{%
\begin{code}
delem {pkh} [] p1 = allNil
delem {pkh} ((pkh' , v') ∷ map) (allCons {{i}} {{is}}) with pkh == pkh'
...| true = is 
...| false = allCons {{i}} {{delem map is}}
\end{code}
}


\newcommand\mGeqlem{%
\begin{code}
geqLem : ∀ {pkh} (map : AccMap) (v : Value)
      -> All (λ y → geq (snd y) emptyValue ≡ true) map
      -> lookup pkh map ≡ Just v
      -> geq v emptyValue ≡ true
\end{code}
}

\newcommand\mGeqlemP{%
\begin{code}
geqLem {pkh} ((pkh' , v') ∷ map) v p1 p2 with pkh == pkh'
geqLem {pkh} ((pkh' , v') ∷ map) v
  (allCons {{i}} {{is}}) refl | true = i
geqLem {pkh} ((pkh' , v') ∷ map) v
  (allCons {{i}} {{is}}) p2 | false = geqLem map v is p2
\end{code}
}


\newcommand\mIVal{%
\begin{code}
initialValidity : ∀ {s par}
  -> par ⊢ s
  -> valid s 
initialValidity {record { datum = tok , [] }}
                (TStart refl p2 p3) = allNil
\end{code}
}

\newcommand\mVal{%
\begin{code}
validity : ∀ {s s' i par}
  -> valid s
  -> par ⊢ s ~[ i ]~> s'
  -> valid s'
\end{code}
}


\newcommand\mValOpen{%
\begin{code}
validity {record { datum = tok , map }}
         {record { datum = .(_ , insert _ emptyValue map) }} p
         (TOpen refl p2 p3 refl p5)
         = (lem map emptyValue refl p)
\end{code}
}


\newcommand\mValClose{%
\begin{code}
validity {record { datum = tok , map }}
         {record { datum = .(_ , delete _ map) }} p
         (TClose refl p2 p3 refl p5) = (delem map p)
\end{code}
}

\newcommand\mValDeposit{%
\begin{code}
validity {record { datum = tok , map }}
         {record { datum = .(_ , insert _ (v + val) map) }} p
         (TDeposit {val = val} {v = v} refl p2 p3 p4 refl p6)
         = lem map (v + val)
           (sumLemma v val (geqLem map v p p3) p4) p
\end{code}

}

\newcommand\mValWithdraw{%
\begin{code}
validity {record { datum = tok , map }}
         {record { datum = .(_ , insert _ (v - val) map) }} p
         (TWithdraw {val = val} {v = v} refl p2 p3 p4 p5 refl refl)
         = (lem map (v - val) (diffLemma v val p5) p)
\end{code}
}

\newcommand\mValTransfer{%
\begin{code}
validity {record { datum = tok , map }}
         {record { datum = .(_ , insert from (vF - val)
                                (insert to (vT + val) map)) }} p
         (TTransfer {par} {from} {to} {val} {vF = vF} {vT = vT}
                    refl p2 p3 p4 p5 p6 p7 refl p9)
         = lem (insert to (vT + val) map) (vF - val) (diffLemma vF val p6)
           (lem map (vT + val) (sumLemma vT val (geqLem map vT p p4) p5) p)
\end{code}
} 

\begin{code}[hide]


-- Validity Proof

\end{code}

\newcommand\mSumVal{%
\begin{code}
sumVal : AccMap -> Value
sumVal [] = emptyValue
sumVal ((k , v) ∷ xs) = v + sumVal xs
\end{code}
}

\newcommand\mInternalVal{%
\begin{code}
internalVal : State -> Value
internalVal s = sumVal (accMap s) + minValue + assetClassValue (threadToken s) 1
\end{code}
}

\begin{code}[hide]


\end{code}

\newcommand\mIValue{%
\begin{code}
iVal : AccMap -> AssetClass -> Value
iVal [] ac = minValue + assetClassValue ac 1
iVal ((k , v) ∷ xs) ac = v + (iVal xs) ac
\end{code}
}

\newcommand\mIValueTwo{%
\begin{code}
internalVal' : State -> Value
internalVal' s = iVal (accMap s) (threadToken s)
\end{code}
}

\newcommand\mIValEq{%
\begin{code}
iVal≡' : ∀ (map : AccMap) (ac : AssetClass)
  -> sumVal map + minValue + assetClassValue ac 1 ≡ iVal map ac
iVal≡' [] ac = refl
iVal≡' ((pkh , v) ∷ map) ac rewrite assocVal v (sumVal map) minValue
  | assocVal v (sumVal map + minValue) (assetClassValue ac 1)
  = cong (λ y → v + y) (iVal≡' map ac)
  
iVal≡ : ∀ (s : State) -> internalVal s ≡ internalVal' s
iVal≡ s = iVal≡' (accMap s) (threadToken s)
\end{code}
}

\begin{code}[hide]

-- Fidelity predicate

\end{code}

\newcommand\mFides{%
\begin{code}
fides : State -> Set
fides s = value s ≡ internalVal s
\end{code}
}

\newcommand\mMBot{%
\begin{code}
maybe⊥ : ∀ {a : Value} -> Nothing ≡ Just a -> ⊥
maybe⊥ ()
\end{code}
}

\newcommand\mMEq{%
\begin{code}
maybe≡ : ∀ {a b : Value} -> Just a ≡ Just b → a ≡ b
maybe≡ refl = refl
\end{code}
}


\newcommand\mIValOne{%
\begin{code}
iValLemma1 : ∀ {pkh} (map : AccMap) (ac : AssetClass)
           -> lookup pkh map ≡ Nothing
           -> iVal map ac ≡ iVal (insert pkh emptyValue map) ac
\end{code}
}

\newcommand\mIValOnep{%
\begin{code}
iValLemma1 {pkh} [] ac p = refl
iValLemma1 {pkh} ((pkh' , v') ∷ map) ac p with pkh == pkh'
...| false = cong (λ a → v' + a) (iValLemma1 map ac p)
...| true = ⊥-elim (maybe⊥ (sym p))
\end{code}
}

\newcommand\mIValTwo{%
\begin{code}
iValLemma2 : ∀ {pkh} (map : AccMap) (ac : AssetClass)
           -> lookup pkh map ≡ Just emptyValue
           -> iVal map ac ≡ iVal (delete pkh map) ac
\end{code}
}

\newcommand\mIValTwop{%
\begin{code}
iValLemma2 [] ac p = refl
iValLemma2 {pkh} ((pkh' , v') ∷ map) ac p with pkh == pkh'
...| false = cong (λ a → v' + a) (iValLemma2 map ac p)
...| true rewrite maybe≡ p = addValIdL (iVal map ac)
\end{code}
}

\newcommand\mIValThree{%
\begin{code}
iValLemma3 : ∀ {pkh v val} (map : AccMap) (ac : AssetClass)
           -> lookup pkh map ≡ Just v
           -> (iVal map ac) + val ≡
              iVal (insert pkh (v + val) map) ac
\end{code}
}

\newcommand\mIValThreep{%
\begin{code}
iValLemma3 [] ac p = ⊥-elim (maybe⊥ p) 
iValLemma3 {pkh} {v} {val} ((pkh' , v') ∷ map) ac p with pkh == pkh'
...| false rewrite (assocVal v' (iVal map ac) val)
     = cong (λ a → v' + a) (iValLemma3 map ac p)
...| true rewrite maybe≡ p | assocVal v (iVal map ac) val
                | commVal (iVal map ac) val
                | assocVal v val (iVal map ac) = refl
\end{code}
}

\newcommand\mIValFour{%
\begin{code}
iValLemma4 : ∀ {from to vF vT val} (map : AccMap) (ac : AssetClass)
           -> lookup from map ≡ Just vF
           -> lookup to map ≡ Just vT
           -> from ≢ to
           -> iVal map ac ≡ iVal (insert from (vF - val)
                           (insert to (vT + val) map)) ac
\end{code}
}

\newcommand\mIValFourp{%
\begin{code}
iValLemma4 {from} {to} {vF} {vT} {val} ((pkh , v) ∷ map) ac p1 p2 p3
  with to == pkh in eq1
iValLemma4 {from} {to} {vF} {vT} {val} ((pkh , v) ∷ map) ac p1 p2 p3
  | true with from == to in eq2
iValLemma4 {from} {to} {vF} {vT} {val} ((pkh , v) ∷ map) ac p1 p2 p3
  | true | true = ⊥-elim (p3 (==to≡ from to eq2))
iValLemma4 {from} {to} {vF} {vT} {val} ((pkh , v) ∷ map) ac p1 p2 p3
  | true | false with from == pkh in eq3
iValLemma4 {from} {to} {vF} {vT} {val} ((pkh , v) ∷ map) ac p1 p2 p3
  | true | false | true 
    rewrite ==to≡ to pkh eq1 | ==to≡ from pkh eq3 = ⊥-elim (p3 refl)
iValLemma4 {from} {to} {vF} {vT} {val} ((pkh , v) ∷ map) ac p1 p2 p3
  | true | false | false
    rewrite assocVal vT val (iVal (insert from (vF - val) map) ac)
    | (maybe≡ p2) | commVal val (iVal (insert from (vF - val) map) ac)
    = cong (λ a → vT + a) (switchSides (iVal map ac) val
    (iVal (insert from (vF - val) map) ac) (iValLemma3 map ac p1))
iValLemma4 {from} {to} {vF} {vT} {val} ((pkh , v) ∷ map) ac p1 p2 p3
  | false with from == pkh in eq2
iValLemma4 {from} {to} {vF} {vT} {val} ((pkh , v) ∷ map) ac p1 p2 p3
  | false | true
    rewrite assocVal vF (negValue val) (iVal (insert to (vT + val) map) ac) 
    | (maybe≡ p1) | commVal (negValue val) (iVal (insert to (vT + val) map) ac) 
    = cong (λ a → vF + a) (switchSides' (iVal map ac) val
    (iVal (insert to (vT + val) map) ac) (iValLemma3 map ac p2))
iValLemma4 {from} {to} {vF} {vT} {val} ((pkh , v) ∷ map) ac p1 p2 p3
  | false | false = cong (λ a → v + a) (iValLemma4 map ac p1 p2 p3)
\end{code}
}


\begin{code}[hide]

-- Lemmas for Fidelity

-- Fidelity Proof

\end{code}

\newcommand\mIFid{%
\begin{code}
initialFidelity : ∀ {s par}
  -> par ⊢ s
  -> fides s
initialFidelity {record { datum = .(_ , []) }}
                (TStart refl p2 p3) = p3 
\end{code}
}

\newcommand\mFid{%
\begin{code}
fidelity : ∀ {s s' i par}
         -> fides s
         -> par ⊢ s ~[ i ]~> s'
         -> fides s'
\end{code}
}

\newcommand\mFidOpen{%
\begin{code}       
fidelity {s@record { datum = tok , map }} {s'} refl
         (TOpen refl p2 p3 refl refl)
         rewrite iVal≡ s | iVal≡ s' = iValLemma1 map tok p3
\end{code}
}

\newcommand\mFidClose{%
\begin{code}
fidelity {s@record { datum = tok , map }} {s'} refl
         (TClose refl p2 p3 refl refl)
         rewrite iVal≡ s | iVal≡ s' = iValLemma2 map tok p3
\end{code}
}

\newcommand\mFidDeposit{%
\begin{code}
fidelity {s@record { datum = tok , map }} {s'} refl
         (TDeposit refl p2 p3 p4 refl refl) 
         rewrite iVal≡ s | iVal≡ s' = iValLemma3 map tok p3
\end{code}
}

\newcommand\mFidWithdraw{%
\begin{code}
fidelity {s@record { datum = tok , map }} {s'} refl
         (TWithdraw refl p2 p3 p4 p5 refl refl)
         rewrite iVal≡ s | iVal≡ s' = iValLemma3 map tok p3
\end{code}
}

\newcommand\mFidTransfer{%
\begin{code}
fidelity {s@record { datum = tok , map }} {s'} refl
         (TTransfer refl p2 p3 p4 p5 p6 p7 refl refl)
         rewrite iVal≡ s | iVal≡ s' = iValLemma4 map tok p3 p4 p7
\end{code}
}

\begin{code}[hide]



-- Combined state invariant predicate


\end{code}

\newcommand\mInvar{%
\begin{code}
invariant : State -> Set
invariant s = (valid s × fides s)
\end{code}
}

\newcommand\mInvarp{%
\begin{code}
initialInvariant : ∀ {s par}
  -> par ⊢ s
  -> invariant s
initialInvariant p = (initialValidity p) , (initialFidelity p)

stateInvariant : ∀ {s s' i par}
  -> invariant s
  -> par ⊢ s ~[ i ]~> s'
  -> invariant s'
stateInvariant (valid , fides) p = validity valid p , fidelity fides p
\end{code}
}

\newcommand\mInvarMulti{%
\begin{code}
multiStepInvariant : ∀ {s s' is par}
  -> invariant s
  -> par ⊢ s ~[ is ]~* s'
  -> invariant s'
multiStepInvariant p nil = p
multiStepInvariant p (cons t ts) = multiStepInvariant (stateInvariant p t) ts
\end{code}
}


\newcommand\mMakeIs{%
\begin{code}
makeIs : AccMap -> List Redeemer
makeIs [] = []
makeIs ((pkh , v) ∷ map) = (Withdraw pkh v) ∷ (Close pkh) ∷ (makeIs map)
\end{code}
}

\newcommand\mLastSig{%
\begin{code}
lastSig : AccMap -> PubKeyHash -> PubKeyHash
lastSig [] pkh = pkh
lastSig ((pkh' , v') ∷ []) pkh = pkh'
lastSig (x ∷ y ∷ map) pkh = lastSig (y ∷ map) pkh
\end{code}
}

\newcommand\mSameLS{%
\begin{code}
sameLastSig : ∀ {x sig sig'} (map : AccMap)
             -> lastSig (x ∷ map) sig ≡ lastSig (x ∷ map) sig'
sameLastSig [] = refl
sameLastSig (y ∷ map) = sameLastSig map
\end{code}
}


\newcommand\mLSLemma{%
\begin{code}
lastSigLemma : ∀ {pkh v sig} (map : AccMap)
              -> lastSig ((pkh , v) ∷ map) sig ≡ lastSig map pkh
lastSigLemma [] = refl
lastSigLemma (x ∷ []) = refl
lastSigLemma (x ∷ y ∷ map) = sameLastSig map
\end{code}
}



\newcommand\mRWLookup{%
\begin{code}
rwLookup : ∀ {b : Bool} {a : Set} { x y : Maybe a }
            -> b ≡ true
            -> (if b then x else y) ≡ x
rwLookup refl = refl
\end{code}
}


\newcommand\mRWID{%
\begin{code}
rwInsertDelete : ∀ {a : AssetClass} {b : Bool} { x y z : AccMap }
            -> b ≡ true
            -> x ≡ z
            -> (a , z) ≡ (a , (if b then x else y))
rwInsertDelete refl refl = refl
\end{code}
}


\newcommand\mRWAM{%
\begin{code}
rwAccMap : ∀ (pkh : PubKeyHash) (val : Value) (map : AccMap)
           -> (pkh , val - val) ∷ map ≡ (pkh , emptyValue) ∷ map
rwAccMap pkh val map rewrite (v-v val) = refl
\end{code}
}

\newcommand\mRWVal{%
\begin{code}
rwVal : ∀ (v1 v2 : Value)
            -> v1 ≡ (v2 + v1) - v2 
rwVal v1 v2 rewrite commVal v2 v1
            | assocVal v1 v2 (negValue v2)
            | v-v v2 = sym (addValIdR v1)
\end{code}
}


\newcommand\mGetG{%
\begin{code}
getGeq : ∀ {x} (map : AccMap)
  -> All (\y -> geq (snd y) emptyValue ≡ true) (x ∷ map)
  -> geq (snd x) emptyValue ≡ true
getGeq map (allCons {{i}} {{is}}) = i
\end{code}
}



\newcommand\mGetV{%
\begin{code}
getValid : ∀ {x} (map : AccMap)
  -> All (\y -> geq (snd y) emptyValue ≡ true) (x ∷ map)
  -> All (\y -> geq (snd y) emptyValue ≡ true) map
getValid map (allCons {{i}} {{is}}) = is
\end{code}
}


\newcommand\mLiqLemma{%
\begin{code}
liqLemma : ∀ {tok} {map : AccMap} (s s' : State) {par}
        -> datum s ≡ (tok , map)
        -> datum s' ≡ (tok , [])
        -> value s' ≡ minValue + assetClassValue tok 1
        -> tsig s' ≡ lastSig map (tsig s)
        -> value s ≡ iVal map tok 
        -> spends s ≡ spends s'
        -> threadTokCS s ≡ threadTokCS s'
        -> valid s
        -> par ⊢ s ~[ (makeIs map) ]~* s'
\end{code}
}

\newcommand\mLiqLemmap{%
\begin{code}
liqLemma record { datum = (tok , []) } s'
  refl refl refl refl refl refl refl p = nil
liqLemma s@record { datum = (tok , (pkh , v) ∷ map') }
      s' refl refl refl refl refl refl refl p
      = cons {s' = st} (TWithdraw refl refl (rwLookup (n=n pkh))
        (getGeq map' p) (geq-refl v) (rwInsertDelete (n=n pkh)
        (rwAccMap pkh v map')) (rwVal (value st) v)) 
        (cons {s' = st'} (TClose refl refl (rwLookup (n=n pkh))
        (rwInsertDelete (n=n pkh) refl) refl )
        (liqLemma st' s' refl refl refl (lastSigLemma map')
        refl refl refl (getValid map' p)))        
\end{code}
}


\newcommand\mLiqLemmaSOne{%
\begin{code}    
      where
      st = record
            { datum = tok , ((pkh , emptyValue) ∷ map')
            ; value = iVal map' tok
            ; tsig = pkh
            ; spends = s .spends
            ; threadTokCS = s .threadTokCS }        
\end{code}
}


\newcommand\mLiqLemmaSTwo{%
\begin{code}    
      st' = record
             { datum = tok , map'
             ; value = iVal map' tok
             ; tsig = pkh
             ; spends = s .spends
             ; threadTokCS = s .threadTokCS }
\end{code}
}


\newcommand\mLiq{%
\begin{code}
liquidity : ∀ (s : State) (par : MParams)
          -> invariant s
          -> ∃[ s' ] ∃[ is ] par ⊢ s ~[ is ]~|* s'
\end{code}
}

\newcommand\mLiqp{%
\begin{code}
liquidity s par (p1 , p2) rewrite iVal≡ s
  = ⟨ s'' , ⟨ (makeIs (accMap s) ++ [ Stop ]) ,
    (fin (liqLemma s s' refl refl refl refl p2 refl refl p1)
    (TStop refl) ) ⟩ ⟩
\end{code}
}


\newcommand\mLiqSOne{%
\begin{code}
  where
  s'' = record
         { datum = ada , []
         ; value = emptyValue
         ; tsig = 0
         ; spends = 0
         ; threadTokCS = 0 }
\end{code}
}


\newcommand\mLiqSTwo{%
\begin{code}
  s' = record
       { datum = threadToken s , []
       ; value = minValue + assetClassValue (threadToken s) 1
       ; tsig = lastSig (accMap s) (s .tsig)
       ; spends = s .spends
       ; threadTokCS = s .threadTokCS }
\end{code}
}


\newcommand\mMVLiq{%
\begin{code}
minValLiquidity : ∀ (s : State) (par : MParams)
          -> invariant s
          -> ∃[ s' ] ∃[ is ]
             ((par ⊢ s ~[ is ]~* s') ×
             (value s' ≡ (minValue + assetClassValue (threadToken s') 1)))
\end{code}
}

\newcommand\mMVLiqp{%
\begin{code}
minValLiquidity s par (p1 , p2) rewrite iVal≡ s
  = ⟨ s' , ⟨ (makeIs (accMap s)) ,
    ((liqLemma s s' refl refl refl refl p2 refl refl p1) , refl) ⟩ ⟩ 
  where
  s' = record
       { datum = threadToken s , []
       ; value = minValue + assetClassValue (threadToken s) 1
       ; tsig = lastSig (accMap s) (s .tsig)
       ; spends = s .spends
       ; threadTokCS = s .threadTokCS }
\end{code}
}


\begin{code}[hide]


       
       
-- Multi-Step transition lemma
lemmaMultiStep : ∀ (s s' s'' : State) (is is' : List Redeemer) {par}
                   -> par ⊢  s  ~[ is  ]~* s'
                   -> par ⊢ s' ~[ is' ]~* s''
                   -> par ⊢ s  ~[ is ++ is' ]~* s''
lemmaMultiStep s .s s'' [] is' nil p2 = p2
lemmaMultiStep s s' s'' (x ∷ is) is' (cons {s' = s'''} p1 p2) p3 = cons p1 (lemmaMultiStep s''' s' s'' is is' p2 p3)


originStateRewrite : ∀ {sig spn tokCS} (par : MParams)
                       (s s' : State) (i : Redeemer)
                 -> par ⊢ s ~[ i ]~> s'
                 -> par ⊢ record
                           { datum = datum s
                           ; value = value s
                           ; tsig = sig
                           ; spends = spn
                           ; threadTokCS = tokCS
                           } ~[ i ]~> s'
                           
originStateRewrite par s s' i (TOpen x x₁ x₂ x₃ x₄)
  = TOpen x x₁ x₂ x₃ x₄
originStateRewrite par s s' i (TClose x x₁ x₂ x₃ x₄)
  = TClose x x₁ x₂ x₃ x₄
originStateRewrite par s s' i (TDeposit x x₁ x₂ x₃ x₄ x₅)
  = TDeposit x x₁ x₂ x₃ x₄ x₅
originStateRewrite par s s' i (TWithdraw x x₁ x₂ x₃ x₄ x₅ x₆)
  = TWithdraw x x₁ x₂ x₃ x₄ x₅ x₆
originStateRewrite par s s' i (TTransfer x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈)
  = TTransfer x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈

targetStateRewrite : ∀ {spn tokCS} (par : MParams) (s s' : State) (i : Redeemer)
                 -> par ⊢ s ~[ i ]~> s'
                 -> par ⊢ s ~[ i ]~> record
                                      { datum = datum s'
                                      ; value = value s'
                                      ; tsig = tsig s'
                                      ; spends = spn
                                      ; threadTokCS = tokCS
                                      }

targetStateRewrite par s s' i (TOpen x x₁ x₂ x₃ x₄)
  = TOpen x x₁ x₂ x₃ x₄
targetStateRewrite par s s' i (TClose x x₁ x₂ x₃ x₄)
  = TClose x x₁ x₂ x₃ x₄
targetStateRewrite par s s' i (TDeposit x x₁ x₂ x₃ x₄ x₅)
  = TDeposit x x₁ x₂ x₃ x₄ x₅
targetStateRewrite par s s' i (TWithdraw x x₁ x₂ x₃ x₄ x₅ x₆)
  = TWithdraw x x₁ x₂ x₃ x₄ x₅ x₆
targetStateRewrite par s s' i (TTransfer x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈)
  = TTransfer x x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈


rwDatum : ∀ {tok : AssetClass} (pkh : PubKeyHash) (v : Value) (map : AccMap)
  -> (tok , insert pkh emptyValue map) ≡
     (tok , insert pkh (v - v) map)
rwDatum pkh v map rewrite v-v v = refl


lookupInsertLemma : ∀ (pkh : PubKeyHash) (v : Value) (map : AccMap)
  -> lookup pkh (insert pkh v map) ≡ Just v
lookupInsertLemma pkh v [] rewrite n=n pkh = refl
lookupInsertLemma pkh v (x ∷ map) with pkh == x .fst in eq
...| True rewrite n=n pkh = refl
...| False rewrite eq = lookupInsertLemma pkh v map

userCanRecoverFunds :
  ∀ {val par} (s : State) (pkh : PubKeyHash)
  -> lookup pkh (accMap s) ≡ Just val
  -> invariant s
  -> ∃[ s' ] ((par ⊢ s ~[ [ Withdraw pkh val ] ]~* s')
     × (lookup pkh (accMap s') ≡ Just emptyValue))
     
userCanRecoverFunds {val} s@record { datum = (tok , map) ; value = v}
  pkh p1 p2 = ⟨ s' , (cons {s' = s'} (TWithdraw refl refl p1
              (geqLem map val (p2 .fst) p1)
              (geq-refl val) (rwDatum pkh val map) refl)
              nil , lookupInsertLemma pkh emptyValue map) ⟩
  where
  s' = record
        { datum = tok , (insert pkh emptyValue map)
        ; value = v - val
        ; tsig = pkh
        ; spends = 0
        ; threadTokCS = 0
        }


skipInsert : ∀ {val} (pkh1 pkh2 : PubKeyHash) (map : AccMap)
             -> pkh1 ≢ pkh2
             -> lookup pkh2 map ≡ lookup pkh2 (insert pkh1 val map)
             
skipInsert pkh1 pkh2 [] p with pkh2 == pkh1 in eq
...| True = ⊥-elim (p (sym (==to≡ pkh2 pkh1 eq)))
...| False = refl
skipInsert pkh1 pkh2 (x ∷ map') p with pkh2 == (x .fst) in eq1
skipInsert pkh1 pkh2 (x ∷ map') p | True with pkh1 == (x .fst) in eq2
skipInsert pkh1 pkh2 (x ∷ map') p | True | True
  rewrite ==to≡ pkh2 (x .fst) eq1 | ==to≡ pkh1 (x .fst) eq2 = ⊥-elim (p refl)
skipInsert pkh1 pkh2 (x ∷ map') p | True | False rewrite eq1 = refl
skipInsert pkh1 pkh2 (x ∷ map') p | False with pkh1 == (x .fst) in eq2
skipInsert pkh1 pkh2 (x ∷ map') p | False | True 
  rewrite sym (==to≡ pkh1 (x .fst) eq2) | eq1 = refl
skipInsert pkh1 pkh2 (x ∷ map') p | False | False rewrite eq1
  = skipInsert pkh1 pkh2 map' p


otherAccountsUnaffectedW :
  ∀ {val} (s s' : State) (par : MParams) (pkh1 pkh2 : PubKeyHash)
  -> par ⊢ s ~[ Withdraw pkh1 val ]~> s'
  -> pkh1 ≢ pkh2
  -> lookup pkh2 (accMap s) ≡ lookup pkh2 (accMap s')
otherAccountsUnaffectedW record {datum = (tok , map)} s' par pkh1 pkh2
  (TWithdraw refl refl c d e refl refl) p2 = skipInsert pkh1 pkh2 map p2

otherAccountsUnaffectedD :
  ∀ {val} (s s' : State) (par : MParams) (pkh1 pkh2 : PubKeyHash)
  -> par ⊢ s ~[ Deposit pkh1 val ]~> s'
  -> pkh1 ≢ pkh2
  -> lookup pkh2 (accMap s) ≡ lookup pkh2 (accMap s')
otherAccountsUnaffectedD record {datum = (tok , map)} s' par pkh1 pkh2
  (TDeposit refl refl c d refl refl) p2 = skipInsert pkh1 pkh2 map p2



checkWithdraw' : AssetClass -> Maybe Value -> PubKeyHash -> Value -> AccMap -> Datum -> Bool
checkWithdraw' tok Nothing _ _ _ _ = false
checkWithdraw' tok (Just v) pkh val map (tok' , map') = geq val emptyValue && geq v val && ((tok' , map') == (tok , insert pkh (v - val) map))

checkDeposit' : AssetClass -> Maybe Value -> PubKeyHash -> Value -> AccMap -> Datum -> Bool
checkDeposit' tok Nothing _ _ _ _ = false
checkDeposit' tok (Just v) pkh val map (tok' , map') = geq val emptyValue && ((tok' , map') == (tok , insert pkh (v + val) map))

checkTransfer' : AssetClass -> Maybe Value -> Maybe Value -> PubKeyHash -> PubKeyHash -> Value -> AccMap -> Datum -> Bool
checkTransfer' tok Nothing _ _ _ _ _ _ = false
checkTransfer' tok (Just vF) Nothing _ _ _ _ _ = false
checkTransfer' tok (Just vF) (Just vT) from to val map (tok' , map') = geq val emptyValue && geq vF val && from /= to &&
                         (tok' , map') == (tok , insert from (vF - val) (insert to (vT + val) map))




\end{code}


\newcommand\pSigRef{%
\begin{code}
sig : ScriptContext -> PubKeyHash
sig = ScriptContext.signature

iRef : ScriptContext -> TxOutRef
iRef = ScriptContext.inputRef
\end{code}
}


\newcommand\pGetS{%
\begin{code}
getS : Datum -> ScriptContext -> State
getS dat ctx = record
             { datum = dat
             ; value = oldValue ctx
             ; tsig = 0 
             ; spends = 0
             ; threadTokCS = 0 }
\end{code}
}


\newcommand\pGetSPrime{%
\begin{code}
getS' : ScriptContext -> State
getS' ctx = record
          { datum = newDatum ctx
          ; value = newValue ctx
          ; tsig = sig ctx
          ; spends = iRef ctx
          ; threadTokCS = 0 }
\end{code}
}


\newcommand\pGetMintS{%
\begin{code}
getMintS : TokenName -> ScriptContext -> State
getMintS tn ctx = record
                { datum = newDatum ctx
                ; value = newValue ctx
                ; tsig = sig ctx
                ; spends = iRef ctx
                ; threadTokCS = ownCurrencySymbol ctx }
\end{code}
}

\newcommand\pGetPar{%
\begin{code}
getPar : TxOutRef -> TokenName -> MParams
getPar oref tn = record
               { uniqueId = oref
               ; threadTokName = tn }
\end{code}
}


\newcommand\pPhase{%
\begin{code}
data Phase : Set where
  Initial  : Phase
  Running  : Phase
  Final    : Phase
\end{code}
}

\newcommand\pArgument{%
\begin{code}
record Argument : Set where
  field
    adr  : Address
    oref : TxOutRef
    tn   : TokenName
    dat  : Datum
    red  : Redeemer
    ctx  : ScriptContext 
open Argument
\end{code}
}

\newcommand\pEquiv{%
\begin{code}
record _≈_ {A : Set} (f : A -> Bool) (R : A -> Set) : Set where
  field to   : ∀ {a} -> f a ≡ true -> R a
        from : ∀ {a} -> R a        -> f a ≡ true
\end{code}
}

\newcommand\pClassifier{%
\begin{code}
classifier : Argument -> Phase
classifier record { ctx = record { mint = +[1+ zero ] } } = Initial
classifier record { ctx = record { mint = +_ zero } } = Running
classifier _ = Final
\end{code}
}

\newcommand\pTotalF{%
\begin{code}
totalF : Argument -> Bool
totalF arg with classifier arg
... | Initial = agdaPolicy (arg .adr) (arg .oref) (arg .tn) tt (arg .ctx)
... | Running = agdaValidator (arg .dat) (arg .red) (arg .ctx) 
... | Final   = agdaValidator (arg .dat) (arg .red) (arg .ctx) &&
                agdaPolicy (arg .adr) (arg .oref) (arg .tn) tt (arg .ctx)
\end{code}
}

\newcommand\pTotalR{%
\begin{code}
totalR : Argument -> Set
totalR arg with classifier arg
\end{code}
}

\newcommand\pTotalRI{%
\begin{code}
... | Initial = getPar (arg .oref) (arg .tn) ⊢ getMintS (arg .tn) (arg .ctx)
                 × continuing (arg .ctx) ≡ true
                 × getMintedAmount (arg .ctx) ≡ 1
                 × checkTokenOutAddr (arg .adr)
                   (ownAssetClass (arg .tn) (arg .ctx)) (arg .ctx) ≡ true
\end{code}
}
\newcommand\pTotalRR{%
\begin{code}
... | Running = getPar (arg .oref) (arg .tn)
                ⊢ getS (arg .dat) (arg .ctx) ~[ (arg .red) ]~> getS' (arg .ctx)
                 × continuing (arg .ctx) ≡ true
                 × checkTokenIn (arg .dat .fst) (arg .ctx) ≡ true
                 × checkTokenOut (arg .dat .fst) (arg .ctx) ≡ true               
\end{code}
}
\newcommand\pTotalRF{%
\begin{code}             
... | Final   = getPar (arg .oref) (arg .tn)
                ⊢ getS (arg .dat) (arg .ctx)  ~[ (arg .red) ]~| getS' (arg .ctx)
                 × continuing (arg .ctx) ≡ false
                 × getMintedAmount (arg .ctx) ≡ -1
                 × checkTokenIn (arg .dat .fst) (arg .ctx) ≡ true
\end{code}
}

\newcommand\pMapEq{%
\begin{code}
==pto≡ : ∀ (a b : PubKeyHash × Value) -> (a == b) ≡ true -> a ≡ b
==pto≡ (fst1 , snd1) (fst2 , snd2) pf
  rewrite (==to≡ fst1 fst2 (get pf))
        | (==vto≡ snd1 snd2 (go (fst1 == fst2) pf)) = refl
        
==mto≡ : ∀ (a b : AccMap) -> (a == b) ≡ true -> a ≡ b
==mto≡ [] [] pf = refl
==mto≡ (x ∷ a) (y ∷ b) pf rewrite (==pto≡ x y (get pf))
  = cong (λ x → y ∷ x) (==mto≡ a b (go (x == y) pf))
\end{code}
}



\newcommand\pMII{%
\begin{code}
mintingImpliesInitial : ∀ (adr : Address) (oref : TxOutRef) (tn : TokenName)
  (top : ⊤) (ctx : ScriptContext)
  -> getMintedAmount ctx ≡ 1
  -> agdaPolicy adr oref tn top ctx ≡ true
  -> (getPar oref tn ⊢ getMintS tn ctx
     × continuing ctx ≡ true
     × getMintedAmount ctx ≡ 1
     × checkTokenOut (ownAssetClass tn ctx) ctx ≡ true)
\end{code}
}

\newcommand\pMIIp{%
\begin{code}
mintingImpliesInitial adr oref tn top ctx@record { outputVal = outputVal ;
  outputDatum = (tok , map) ; continues = continues ; inputRef = inputRef ;
  mint = + 1 ; tokCurrSymbol = cs } refl pf
  rewrite ==mto≡ map [] (go ((cs , tn) == tok)
          (get (go (inputRef == oref) (go continues pf))))
  | sym (==tto≡ (cs , tn) tok
    (get (get (go (inputRef == oref) (go continues pf)))))
  = (TStart refl (==to≡ inputRef oref (get (go continues pf)))
    (==vto≡ outputVal (minValue + assetClassValue (cs , tn) 1)
    (go (checkTokenOutAddr adr (cs , tn) ctx) (go (checkDatum adr tn ctx)
    (go (inputRef == oref) (go continues pf))))) , get pf , refl ,
    (get (go (checkDatum adr tn ctx)
    (go (inputRef == oref) (go continues pf)))))
\end{code}
}


\newcommand\pVIR{%
\begin{code}
validatorImpliesRunning :
  ∀ {par} (d : Datum) (i : Redeemer) (ctx : ScriptContext) 
  -> getMintedAmount ctx ≡ 0
  -> agdaValidator d i ctx ≡ true
  -> (par ⊢ getS d ctx ~[ i ]~> getS' ctx
     × continuing ctx ≡ true
     × checkTokenIn (d .fst) ctx ≡ true
     × checkTokenOut (d .fst) ctx ≡ true)
\end{code}
}


\newcommand\pBIF{%
\begin{code}
bothImplyFinal : ∀ {par} (d : Datum) (adr : Address) (oref : TxOutRef)
  (tn : TokenName) (i : Redeemer) (ctx : ScriptContext) 
  -> getMintedAmount ctx ≡ -1
  -> (agdaValidator d i ctx && agdaPolicy adr oref tn tt ctx) ≡ true
  -> (par ⊢ getS d ctx ~[ i ]~| getS' ctx
     × continuing ctx ≡ false
     × getMintedAmount ctx ≡ -1
     × checkTokenIn (d .fst) ctx ≡ true )
\end{code}
}

\newcommand\pBIFpo{%
\begin{code}
bothImplyFinal d adr oref tn (Open pkh)
  ctx@record { continues = false } refl p2
  = ⊥-elim (get⊥ (sym (go (checkTokenOut (d .fst) ctx)
    (go (checkTokenIn (d .fst) ctx) (get p2)))))
bothImplyFinal d adr oref tn i@(Open pkh)
  ctx@record { continues = true } refl p2
  = ⊥-elim (get⊥ (sym (go (agdaValidator d i ctx) p2) ))
\end{code}
}

\newcommand\pBIFps{%
\begin{code}
bothImplyFinal d adr oref tn Stop ctx refl p2
  = (TStop (==mto≡ (snd d) [] (go (not (continuing ctx))
    (go (checkTokenIn (d .fst) ctx) (get p2)))) ,
    (unNot (get (go (checkTokenIn (d .fst) ctx) (get p2)))) ,
    refl , (get (get p2)))
\end{code}
}



\newcommand\pBIFrest{%
\begin{code}
bothImplyFinal d adr oref tn (Close pkh) ctx@record { continues = false } refl p2 = ⊥-elim (get⊥ (sym (go (checkTokenOut (d .fst) ctx) (go (checkTokenIn (d .fst) ctx) (get p2)))))
bothImplyFinal d adr oref tn i@(Close pkh) ctx@record { continues = true } refl p2 = ⊥-elim (get⊥ (sym (go (agdaValidator d i ctx) p2) ))
bothImplyFinal d adr oref tn (Withdraw pkh v) ctx@record { continues = false } refl p2 = ⊥-elim (get⊥ (sym (go (checkTokenOut (d .fst) ctx) (go (checkTokenIn (d .fst) ctx) (get p2)))))
bothImplyFinal d adr oref tn i@(Withdraw pkh v) ctx@record { continues = true } refl p2 = ⊥-elim (get⊥ (sym (go (agdaValidator d i ctx) p2) ))
bothImplyFinal d adr oref tn (Deposit pkh v) ctx@record { continues = false } refl p2 = ⊥-elim (get⊥ (sym (go (checkTokenOut (d .fst) ctx) (go (checkTokenIn (d .fst) ctx) (get p2)))))
bothImplyFinal d adr oref tn i@(Deposit pkh v) ctx@record { continues = true } refl p2 = ⊥-elim (get⊥ (sym (go (agdaValidator d i ctx) p2) ))
bothImplyFinal d adr oref tn (Transfer from to v) ctx@record { continues = false } refl p2 = ⊥-elim (get⊥ (sym (go (checkTokenOut (d .fst) ctx) (go (checkTokenIn (d .fst) ctx) (get p2)))))
bothImplyFinal d adr oref tn i@(Transfer from to v) ctx@record { continues = true } refl p2 = ⊥-elim (get⊥ (sym (go (agdaValidator d i ctx) p2) ))
\end{code}
}


             
\newcommand\pTEQ{%
\begin{code}
totalEquiv : totalF ≈ totalR
\end{code}
}

\newcommand\pMapMap{%
\begin{code}
map=map : ∀ (map : AccMap) -> (map == map) ≡ true
map=map [] = refl
map=map ((tok , val) ∷ map) rewrite n=n tok | v=v val = map=map map
\end{code}
}



\newcommand\pIIM{%
\begin{code}
initialImpliesMinting : ∀ (adr : Address) (oref : TxOutRef) (tn : TokenName)
  (top : ⊤) (ctx : ScriptContext)
  -> (getPar oref tn ⊢ getMintS tn ctx
     × continuing ctx ≡ true
     × getMintedAmount ctx ≡ 1
     × checkTokenOut (ownAssetClass tn ctx) ctx ≡ true)
  -> agdaPolicy adr oref tn top ctx ≡ true
\end{code}
}

\newcommand\pRIV{%
\begin{code}
runningImpliesValidator :
  ∀ {par} (d : Datum) (i : Redeemer) (ctx : ScriptContext)
  -> (par ⊢ getS d ctx ~[ i ]~> getS' ctx
     × continuing ctx ≡ true
     × checkTokenIn (d .fst) ctx ≡ true
     × checkTokenOut (d .fst) ctx ≡ true)
  -> agdaValidator d i ctx ≡ true
\end{code}
}


\newcommand\pRIVp{%
\begin{code}
runningImpliesValidator (tok , map) (Open pkh)
  record { inputVal = inputVal }
  ((TOpen refl refl p3 refl refl) , refl , p7 , p8)
  rewrite p3 | n=n pkh | map=map (insert pkh emptyValue map)
          | v=v inputVal | t=t tok | p7 | p8 = refl
runningImpliesValidator (tok , map) (Close pkh)
  record { inputVal = inputVal }
  ((TClose refl refl p3 refl refl) , refl , p7 , p8)
  rewrite p3 | n=n pkh | map=map (delete pkh map)
          | v=v inputVal | t=t tok | p7 | p8 = refl
runningImpliesValidator (tok , map) (Deposit pkh val)
  record { inputVal = inputVal }
  ((TDeposit {v = v} refl refl p3 p4 refl refl) , refl , p8 , p9)
  rewrite p3 | n=n pkh | v=v (inputVal + val)
          | map=map (insert pkh (v + val) map)
          | p4 | t=t tok | p8 | p9 = refl
runningImpliesValidator (tok , map) (Withdraw pkh val)
  record { inputVal = inputVal }
  ((TWithdraw {v = v} refl refl p3 p4 p5 refl refl) , refl , p9 , p10)
  rewrite p3 | n=n pkh | v=v (inputVal - val)
          | map=map (insert pkh (v - val) map)
          | p4 | p5 | t=t tok | p9 | p10 = refl
runningImpliesValidator (tok , map) (Transfer from to val)
  record { inputVal = inputVal }
  ((TTransfer {vF = vF} {vT = vT} refl refl p3 p4 p5 p6 p7 refl refl) ,
  refl , p11 , p12)
  rewrite p3 | p4 | ≢to/= from to p7 | n=n from | v=v inputVal
          | map=map (insert from (vF - val) (insert to (vT + val) map))
          | p5 | p6 | t=t tok | p11 | p12 = refl
\end{code}
}

\newcommand\pFIB{%
\begin{code}
finalImpliesBoth : ∀ {tn par i} (d : Datum) (adr : Address)
  (oref : TxOutRef) (ctx : ScriptContext)   
  -> (par ⊢ getS d ctx ~[ i ]~| getS' ctx
      × continuing ctx ≡ false
      × getMintedAmount ctx ≡ -1
      × checkTokenIn (d .fst) ctx ≡ true)
  -> (agdaValidator d i ctx && agdaPolicy adr oref tn tt ctx) ≡ true
\end{code}
}


\begin{code}[hide]
-- The Equivalence Relation



-- The Validator as a function returning a boolean





-- The State Transition System as a relation





-- Lemmas and helper functions for validator returning true implies transition



-- Performing a transition implies that the validator returns true



-- Being in the initial model state implies we can mint a token
initialImpliesMinting adr oref tn top record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , l) ; signature = signature ; continues = continues ; inputRef = inputRef ; tokCurrSymbol = cs } ((TStart refl refl p4) , refl , refl , p7)
  rewrite sym p4 | v=v outputVal | n=n oref | t=t tok | p7  = refl 

-- Getting to the terminal state implies that the validator returns true and a token can be burned
finalImpliesBoth d adr oref ctx ((TStop refl) , refl , refl , p4) rewrite p4 = refl



--Validator returning true implies we can perform a transition
validatorImpliesRunning (tok , map) (Open pkh) ctx iv pf with lookup pkh map in eq
validatorImpliesRunning (tok , map) (Open pkh) ctx iv pf | Just _ = ⊥-elim (&&4false (checkTokenIn tok ctx) (checkTokenOut tok ctx) (continuing ctx) (sig ctx == pkh) pf)
validatorImpliesRunning (tok , map) (Open pkh) ctx iv pf | Nothing with newDatum ctx in eq2
validatorImpliesRunning (tok , map) (Open pkh) ctx iv pf | Nothing | tok' , map'
     rewrite (==tto≡ tok' tok (get (get (go (sig ctx == pkh) ((go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))))
             | ==mto≡ map' (insert pkh emptyValue map) (go (tok' == tok) (get (go (sig ctx == pkh) 
             (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))) 
             = (TOpen refl ((==to≡ (sig ctx) pkh (get (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))) )
               eq eq2 (==vto≡ (newValue ctx) (oldValue ctx) (go ((tok' , map') == (tok , insert pkh emptyValue map)) (go (sig ctx == pkh) (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))) , (get (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))) , (get pf) , (get (go (checkTokenIn tok ctx) pf)))  
validatorImpliesRunning (tok , map) (Close pkh) ctx iv pf with lookup pkh map in eq
validatorImpliesRunning (tok , map) (Close pkh) ctx iv pf | Nothing = ⊥-elim (&&4false (checkTokenIn tok ctx) (checkTokenOut tok ctx) (continuing ctx) (sig ctx == pkh) pf) 
validatorImpliesRunning (tok , map) (Close pkh) ctx iv pf | Just v with newDatum ctx in eq2
validatorImpliesRunning (tok , map) (Close pkh) ctx iv pf | Just v | tok' , map' rewrite
            ==vto≡ v emptyValue (get (go (sig ctx == pkh)
            (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))
            | ==tto≡ tok' tok (get (get (go (v == emptyValue) (go (sig ctx == pkh) (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))))
            | ==mto≡ map' (delete pkh map) (go (tok' == tok) (get (go (v == emptyValue) (go (sig ctx == pkh) 
            (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))) 
            = (TClose refl (==to≡ (sig ctx) pkh (get (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))
              eq eq2 (==vto≡ (newValue ctx) (oldValue ctx) (go ( (tok' , map') == (tok , delete pkh map)) (go (v == emptyValue)
              (go (sig ctx == pkh) (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))) , (get (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))) , (get pf) , (get (go (checkTokenIn tok ctx) pf))) 
validatorImpliesRunning (tok , map) (Withdraw pkh val) ctx iv pf with lookup pkh map in eq
validatorImpliesRunning (tok , map) (Withdraw pkh val) ctx iv pf | Nothing = ⊥-elim (&&4false (checkTokenIn tok ctx) (checkTokenOut tok ctx) (continuing ctx) (sig ctx == pkh) pf)
validatorImpliesRunning (tok , map) (Withdraw pkh val) ctx iv pf | Just v with newDatum ctx in eq2
validatorImpliesRunning (tok , map) (Withdraw pkh val) ctx iv pf | Just v | tok' , map'
  rewrite (==tto≡ tok' tok (get (go (geq v val) (go (geq val emptyValue) (get (go (sig ctx == pkh)
             (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))))))
             | (==mto≡ map' (insert pkh (v - val) map)
             (go (tok' == tok) (go (geq v val) (go (geq val emptyValue) (get (go (sig ctx == pkh)
             (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))))))
            = (TWithdraw refl (==to≡ (sig ctx) pkh (get (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))
            eq (get (get (go (sig ctx == pkh) (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))
            (get (go (geq val emptyValue) (get (go (sig ctx == pkh) (go (continuing ctx)
            (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))) eq2 
            ((==vto≡ (newValue ctx) ((oldValue ctx) - val) (go (checkWithdraw' tok (Just v) pkh val map (tok' , map'))
             ((go (sig ctx == pkh) (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))) ) , (get (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))) , (get pf) , (get (go (checkTokenIn tok ctx) pf))) 

validatorImpliesRunning (tok , map) (Deposit pkh val) ctx iv pf with lookup pkh map in eq
validatorImpliesRunning (tok , map) (Deposit pkh val) ctx iv pf | Nothing = ⊥-elim (&&4false (checkTokenIn tok ctx) (checkTokenOut tok ctx) (continuing ctx) (sig ctx == pkh) pf)
validatorImpliesRunning (tok , map) (Deposit pkh val) ctx iv pf | Just v with newDatum ctx in eq2
validatorImpliesRunning (tok , map) (Deposit pkh val) ctx iv pf | Just v | tok' , map'
  rewrite (==tto≡ tok' tok (get (go (geq val emptyValue) (get (go (sig ctx == pkh) (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))))
             | ==mto≡ map' (insert pkh (v + val) map)
             (go (tok' == tok) (go (geq val emptyValue)  (get (go (sig ctx == pkh)
             (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))))
             = (TDeposit refl (==to≡ (sig ctx) pkh (get (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))
             eq (get (get (go (sig ctx == pkh) (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))
             eq2 (==vto≡ (newValue ctx) ((oldValue ctx) + val) (go (checkDeposit' tok (Just v) pkh val map (tok' , map'))
             ((go (sig ctx == pkh) (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))) , (get (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))) , (get pf) , (get (go (checkTokenIn tok ctx) pf))) 

validatorImpliesRunning (tok , map) (Transfer from to val) ctx iv pf with lookup from map in eq1
validatorImpliesRunning (tok , map) (Transfer from to val) ctx iv pf | Nothing
  = ⊥-elim (&&4false (checkTokenIn tok ctx) (checkTokenOut tok ctx) (continuing ctx) (sig ctx == from) pf)
validatorImpliesRunning (tok , map) (Transfer from to val) ctx iv pf | Just vF with lookup to map in eq2
validatorImpliesRunning (tok , map) (Transfer from to val) ctx iv pf | Just vF | Nothing
  = ⊥-elim (&&4false (checkTokenIn tok ctx) (checkTokenOut tok ctx) (continuing ctx) (sig ctx == from) pf)
validatorImpliesRunning (tok , map) (Transfer from to val) ctx iv pf | Just vF | Just vT with newDatum ctx in eq3
validatorImpliesRunning (tok , map) (Transfer from to val) ctx iv pf | Just vF | Just vT | tok' , map'
  rewrite (==tto≡ tok' tok (get (go (from /= to) (go (geq vF val) (go (geq val emptyValue) (get (go (sig ctx == from)
  (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))))))
  | ==mto≡ map' (insert from (vF - val) (insert to (vT + val) map))
  (go (tok' == tok) (go (from /= to) (go (geq vF val) (go (geq val emptyValue) (get (go (sig ctx == from)
  (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))))))
    = (TTransfer refl (==to≡ (sig ctx) from (get (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))) eq1 eq2
    (get (get (go (sig ctx == from) (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))
    (get (go (geq val emptyValue) (get (go (sig ctx == from) 
    (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))))
    (/=to≢ from to (get (go (geq vF val) (go (geq val emptyValue) (get (go (sig ctx == from)
    (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))))) eq3  
    (==vto≡ (newValue ctx) (oldValue ctx) (go (checkTransfer' tok (Just vF) (Just vT) from to val map (tok' , map')) (go (sig ctx == from) (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))) , (get (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))) , (get pf) , (get (go (checkTokenIn tok ctx) pf))) 
validatorImpliesRunning (tok , map) Stop ctx refl pf = ⊥-elim (get⊥ (sym (go (checkTokenIn tok ctx) pf)))


-- Minting the token implies we are in the initial state of our model


-- Validator returning true and burning a token implies we are in the terminal state 


-- Lemma for when the input is Stop



-- The proof of equivalence


\end{code}


\newcommand\pTEQto{%
\begin{code}
totalEquiv = record
  { to = λ { { arg@record { dat = dat ; red = red ; ctx =
               ctx@record { mint = (+_ zero) } } } pf
               → validatorImpliesRunning dat red ctx refl pf ;
             { arg@record { adr = adr ; oref = oref ; tn = tn ;
               ctx = ctx@record { mint = +[1+ zero ] } } } pf
               → mintingImpliesInitial adr oref tn tt ctx refl pf ;
             { arg@record { dat = dat ; red = red ; ctx =
               ctx@record { mint = +[1+ N.suc n ] } } } pf
               → ⊥-elim (&&false (agdaValidator dat red ctx) pf) ;
             { arg@record { dat = dat ; adr = adr; oref = oref; red = red ;
               tn = tn ; ctx = ctx@record { mint = (negsuc zero) } } } pf
               → bothImplyFinal dat adr oref tn red ctx refl pf ;
             { arg@record { dat = dat ; red = red ; ctx =
               ctx@record { mint = (negsuc (N.suc n)) } } } pf
               → ⊥-elim (&&false (agdaValidator dat red ctx) pf) }
\end{code}
}

\newcommand\pTEQfrom{%
\begin{code}
  ; from = λ { { arg@record { dat = dat ; red = red ; ctx =
                 ctx@record { mint = (+_ zero) } } } pf
                 → runningImpliesValidator dat red ctx pf ;
               { arg@record { adr = adr ; oref = oref ; tn = tn ; ctx =
                 ctx@record { mint = +[1+ zero ] } } } pf
                 → initialImpliesMinting adr oref tn tt ctx pf ;
               { arg@record { ctx = ctx@record { mint = +[1+ N.suc n ] } } }
                 (p1 , p2 , () , p4) ;
               { arg@record { adr = adr ; oref = oref ; dat = dat ;
                 ctx = ctx@record { mint = (negsuc zero) } } } pf
                 → finalImpliesBoth {0} dat adr oref ctx pf ;
               { arg@record { ctx = ctx@record { mint = (negsuc (N.suc n)) } } }
                 (p1 , p2 , () , p4) } }
\end{code}
}
