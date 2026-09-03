\begin{code}[hide]
open import Validators.MultiSigLatex
open import Lib
open import Value

open import Agda.Builtin.Char
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
import Data.Nat as N
import Data.Nat.Properties as N
open import Agda.Builtin.Int
open import Agda.Builtin.Nat renaming (_==_ to eqNat; _<_ to ltNat; _+_ to addNat; _-_ to monusNat; _*_ to mulNat)
open import Data.List
open import Data.List.Properties
open import Data.List.Relation.Unary.Any
open import Data.List.Relation.Unary.All as All
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.Core
open import Data.Empty
open import Data.Sum.Base
open import Data.Product using ( ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩; _×_ to _xx_)
open import Haskell.Prim hiding (⊥ ; Any ; All) 
open import Haskell.Prim.Integer
open import Haskell.Prim.Bool
open import Haskell.Prim.Eq
open import Haskell.Prim.Ord
open import Haskell.Prim.Maybe
open import Haskell.Prim.Tuple
open import Haskell.Prim.Foldable using (elem)
open import Haskell.Prim.Ord using (_<=_ ; _>=_)
open import Haskell.Prim using (lengthNat)
open import Haskell.Prelude using (lookup; _-_; _+_)

open import ProofLib

module Proofs.MultiSigProofsLatex where

-- Model and proofs for the Multi-Signature contract


-- Extra definitions necessary for the model
\end{code}

\newcommand\msUnique{%
\begin{code}
_∈_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∈ xs = Any (x ≡_) xs

_∉_ : ∀ {A : Set} (x : A) (xs : List A) → Set
x ∉ xs = ¬ (x ∈ xs)

data Unique {a : Set} : List a → Set where
  root : Unique []
  _::_ : {x : a} {l : List a} -> x ∉ l -> Unique l -> Unique (x ∷ l)
\end{code}
}

\begin{code}[hide]



-- The States of the State Transition System
\end{code}

\newcommand\msState{%
\begin{code}
record State : Set where
  field
    datum       : Datum
    value       : Value  
    outVal      : Value
    interval    : Interval
    tsig        : PubKeyHash
    spends      : TxOutRef
    threadTokCS : CurrencySymbol
open State
\end{code}
}

\begin{code}[hide]

  
-- Model paramets consisting of the combined parameters of the validator and minting policy


\end{code}

\newcommand\msMParams{%
\begin{code}
record MParams : Set where
    field
        uniqueId         : TxOutRef
        threadTokName    : TokenName
        authSigs         : List PubKeyHash
        minSigs          : Nat
        maxWait          : Integer
open MParams public
\end{code}
}

\begin{code}[hide]

-- Transition Rules of the State Transition System

--The Initial Transition
\end{code}

\newcommand\msInitial{%
\begin{code}
data _⊢_ : MParams -> State -> Set where
  TStart : ∀ {par s}
    -> datum s ≡ ((threadTokCS s , threadTokName par) , Holding )
    -> geq (value s) x2MinValue ≡ true
    -> uniqueId par ≡ spends s
    -> noDups (authSigs par) ≡ true
    -> (lengthNat (authSigs par) >= (minSigs par)) ≡ true
    -> (maxWait par > 0) ≡ true 
    -------------------
    -> par ⊢ s
\end{code}
}

\begin{code}[hide]


--The Running Transitions
\end{code}

\newcommand\msPropose{%
\begin{code}
data _⊢_~[_]~>_ : MParams -> State -> Redeemer -> State -> Set where 
  TPropose : ∀ {v pkh d tok s s' par} 
    -> geq (value s) (v + minValue) ≡ true
    -> geq v minValue ≡ true
    -> datum s ≡ (tok , Holding)
    -> datum s' ≡ (tok , Collecting v pkh d [])
    -> value s' ≡ value s
    -> before (toPOSIXTime (d - (maxWait par))) (interval s') ≡ true 
    -------------------
    -> par ⊢ s ~[ (Propose v pkh d) ]~> s'
\end{code}
}

\newcommand\msAdd{%
\begin{code}
  TAdd : ∀ {sig par s s' v tok pkh d sigs} 
    -> sig ∈ (authSigs par)
    -> tsig s' ≡ sig
    -> datum s ≡ (tok , Collecting v pkh d sigs)
    -> datum s' ≡ (tok , Collecting v pkh d (insert sig sigs))
    -> value s' ≡ value s
    -------------------
    -> par ⊢ s ~[ (Add sig) ]~> s'
\end{code}
}

\newcommand\msPay{%
\begin{code}
  TPay : ∀ {v pkh tok d sigs s s' par} 
    -> length sigs N.≥ minSigs par
    -> datum s ≡ (tok , Collecting v pkh d sigs)
    -> datum s' ≡ (tok , Holding)
    -> value s' + v ≡ value s
    -> outVal s' ≡ v
    -------------------
    -> par ⊢ s ~[ Pay ]~> s'
\end{code}
}

\newcommand\msCancel{%
\begin{code}
  TCancel : ∀ {s s' par v pkh d sigs tok} 
    -> before (toPOSIXTime d) (interval s') ≡ true 
    -> datum s ≡ (tok , Collecting v pkh d sigs)
    -> datum s' ≡ (tok , Holding)
    -> value s' ≡ value s 
    -------------------
    -> par ⊢ s ~[ Cancel ]~> s'
\end{code}
}

\begin{code}[hide]


--The Final Transition
\end{code}

\newcommand\msFinal{%
\begin{code}
data _⊢_~[_]~|_ : MParams -> State -> Redeemer -> State -> Set where
  TStop : ∀ {par s s' tok}
    -> datum s ≡ ( tok , Holding )
    -> (lovelaces x2MinValue > lovelaces (value s)) ≡ true
    -------------------
    -> par ⊢ s ~[ Stop ]~| s'
\end{code}
}

\begin{code}[hide]




--Valid State
\end{code}

\newcommand\msValid{%
\begin{code}
data valid : State -> Set where
  Hol : ∀ {s tok}
    -> datum s ≡ (tok , Holding) 
    ----------------
    -> valid s
  Col : ∀ {s v pkh d sigs tok}
    -> datum s ≡ ( tok , Collecting v pkh d sigs )
    -> geq (value s) (v + minValue) ≡ true
    -> geq v minValue ≡ true
    -> Unique sigs
    --------------------------------
    -> valid s
\end{code}
}

\begin{code}[hide]


--Multi-Step Transition
data _⊢_~[_]~*_ : MParams -> State -> List Redeemer -> State -> Set where

  nil : ∀ { s par }
    ------------------
    -> par ⊢ s ~[ [] ]~* s

  cons : ∀ { par s s' s'' i is }
    -> par ⊢ s ~[ i ]~> s'
    -> par ⊢ s' ~[ is ]~* s''
    -------------------------
    -> par ⊢ s ~[ (i ∷ is) ]~* s''

data _⊢_~[_]~|*_ : MParams -> State -> List Redeemer -> State -> Set where

  fin : ∀ { par s s' s'' is i }
    -> par ⊢ s ~[ is ]~* s'
    -> par ⊢ s' ~[ i ]~| s''
    ---------------------------------
    -> par ⊢ s ~[ (is ++ [ i ]) ]~|* s''

--Valid Parameters
\end{code}

\newcommand\msValidP{%
\begin{code}
validP : MParams -> Set 
validP par = Unique (authSigs par) × length (authSigs par) N.≥ minSigs par ×
  (ltInteger (pos 0) (maxWait par) ≡ true)
\end{code}
}

\newcommand\msInvariant{%
\begin{code}
invariant = valid
\end{code}
}

\newcommand\msValidityLemmas{%
\begin{code}
insertPreservesUniqueness : ∀ {sig sigs}
  -> Unique sigs -> Unique (insert sig sigs)

noDups->Unique : ∀ (l : List PubKeyHash) -> noDups l ≡ true -> Unique l
\end{code}
}

\begin{code}[hide]

--State Validity sub-lemmas
reduce∈ : ∀ {A : Set} {x y : A} {xs} -> y ∈ (x ∷ xs) -> y ≢ x -> y ∈ xs
reduce∈ (here px) p2 = ⊥-elim (p2 px)
reduce∈ (there p1) p2 = p1 

insertPreserves∈ : ∀ {x y zs}
  -> x ∈ insert y zs -> (y == x) ≡ false -> x ∈ zs
insertPreserves∈ {x} {y} {zs = []} (here px) p2 rewrite px = ⊥-elim (n≠n y p2)
insertPreserves∈ {x} {y} {z ∷ zs} p1 p2 with y == x in eq1
...| true =  ⊥-elim (get⊥ p2)
...| false with y == z in eq2
...| true = p1 
...| false with x == z in eq3
...| true rewrite ==to≡ x z eq3 = here refl 
...| false = there (insertPreserves∈ (reduce∈ p1 (λ {refl → n≠n z eq3})) eq1)

insertPreservesUniqueness root = (λ ()) :: root
insertPreservesUniqueness {sig} {(x ∷ xs)} (p :: ps) with sig == x in eq
...| false = (λ z → p (insertPreserves∈ z eq)) :: (insertPreservesUniqueness ps)
...| true = p :: ps

noDupsLemma : ∀ {x : PubKeyHash} {ys : List PubKeyHash} ->
  not (elem x ys) ≡ true -> x ∉ ys
noDupsLemma {x} {[]} p = λ ()
noDupsLemma {x} {y ∷ ys} p with x == y in eq
...| True = ⊥-elim (get⊥ (sym p))
...| False = λ { (here refl) → ⊥-elim (n≠n x eq) ; (there z) → noDupsLemma p z}

noDups->Unique [] p = root
noDups->Unique (x ∷ []) p = (λ ()) :: root
noDups->Unique (x ∷ y ∷ l) p = (noDupsLemma (get p)) :: noDups->Unique (y ∷ l) (go (not (elem x (y ∷ l))) p)

--State Validity Invariants
\end{code}

\newcommand\msInitialValidity{%
\begin{code}
validStateInitial : ∀ {s par}
  -> par ⊢ s
  -> valid s
validStateInitial (TStart p1 p2 p3 p4 p5 p6) = Hol p1
\end{code}
}

\newcommand\msParamValidity{%
\begin{code}
validParamsInitial : ∀ {s par}
  -> par ⊢ s
  -> validP par
validParamsInitial {par = par} (TStart p1 p2 p3 p4 p5 p6)
  = noDups->Unique (authSigs par) p4 ,
    lengthNatToLength (minSigs par) (par .authSigs) p5 , p6
\end{code}
}

\newcommand\msRunningValidity{%
\begin{code}
validStateTransition : ∀ {s s' : State} {i par}
  -> valid s
  -> par ⊢ s ~[ i ]~> s'
  -> valid s'
validStateTransition iv (TPropose p1 p2 p3 p4 refl p6) = Col p4 p1 p2 root
validStateTransition (Hol refl) (TAdd p1 p2 () p4 p5)
validStateTransition (Col refl pf2 pf3 pf4) (TAdd p1 refl refl refl refl)
  = Col refl pf2 pf3 (insertPreservesUniqueness pf4)
validStateTransition iv (TPay p1 p2 p3 p4 p5) = Hol p3 
validStateTransition iv (TCancel p1 p2 p3 p4) = Hol p3
\end{code}
}

\begin{code}[hide]



--Prop1 sub-lemmas and helper functions
\end{code}

\newcommand\msMakeIs{%
\begin{code}
makeIs : List PubKeyHash -> List Redeemer
makeIs [] = []
makeIs (x ∷ pkhs) = Add x ∷ makeIs pkhs
\end{code}
}

\newcommand\msInsertList{%
\begin{code}
insertList : List PubKeyHash -> List PubKeyHash -> List PubKeyHash
insertList [] sigs = sigs
insertList (x ∷ asigs) sigs = insertList asigs (insert x sigs)
\end{code}
}

\newcommand\msFinalSig{%
\begin{code}
finalSig : PubKeyHash -> List PubKeyHash -> PubKeyHash
finalSig base [] = base
finalSig base (pkh ∷ []) = pkh
finalSig base (pkh1 ∷ pkh2 ∷ ls) = finalSig base (pkh2 ∷ ls)
\end{code}
}

\newcommand\msPropLemmas{%
\begin{code}
appendLemma : ∀ (x : PubKeyHash) (a b : List PubKeyHash)
  -> a ++ x ∷ b ≡ (a ++ x ∷ []) ++ b

∈lemma : ∀ (xs ys : List PubKeyHash) (z : PubKeyHash) -> z ∈ (xs ++ z ∷ ys)

finalSigLemma : ∀ (pkh x : PubKeyHash) (xs : List PubKeyHash)
  -> finalSig pkh (x ∷ xs) ≡ finalSig x xs
\end{code}
}

\newcommand\msProp{%
\begin{code}
prop : ∀ {v pkh d sigs tok} (s s' : State) (par : MParams)
  (asigs asigs' asigs'' : List PubKeyHash)
  -> asigs ≡ (authSigs par)
  -> asigs ≡ (asigs' ++ asigs'')
  -> datum s ≡ (tok , Collecting v pkh d sigs)
  -> datum s' ≡ (tok , Collecting v pkh d (insertList asigs'' sigs))
  -> outVal s ≡ outVal s' 
  -> interval s ≡ interval s'
  -> value s ≡ value s'
  -> spends s ≡ spends s'
  -> threadTokCS s ≡ threadTokCS s'
  -> tsig s' ≡ finalSig (tsig s) asigs''
  -> par ⊢ s ~[ makeIs asigs'' ]~* s'
\end{code}
}

\newcommand\msPropP{%
\begin{code}
prop {v} {pkh} {d} {sigs} {tok} s1 s2 par .(asigs1 ++ []) asigs1 []
  refl refl refl refl refl refl refl refl refl refl = nil
prop {v} {pkh} {d} {sigs} {tok} s1 s2 par
  .(asigs1 ++ x ∷ asigs2) asigs1 (x ∷ asigs2)
  refl refl refl refl refl refl refl refl refl refl
  = cons (TAdd (∈lemma asigs1 asigs2 x) refl refl refl refl)
    (prop s' s2 par (asigs1 ++ x ∷ asigs2) (asigs1 ++ [ x ]) asigs2 refl
    (appendLemma x asigs1 asigs2) refl refl refl refl refl refl refl
    (finalSigLemma (tsig s1) x asigs2))
    where
      s' = record
            { datum = tok , Collecting v pkh d (insert x sigs)
            ; value = s1 .value
            ; outVal = s1 .outVal
            ; interval = s1 .interval
            ; tsig = x
            ; spends = s1 .spends
            ; threadTokCS = s1 .threadTokCS
            }
\end{code}
}


\newcommand\msPropOne{%
\begin{code}
prop1 : ∀ { v pkh d sigs tok } (s s' : State) (par : MParams)
  -> datum s ≡ (tok , Collecting v pkh d sigs)
  -> datum s' ≡ (tok , Collecting v pkh d (insertList (authSigs par) sigs))
  -> outVal s ≡ outVal s'
  -> interval s ≡ interval s'
  -> value s ≡ value s'
  -> spends s ≡ spends s'
  -> threadTokCS s ≡ threadTokCS s'
  -> tsig s' ≡ finalSig (tsig s) (authSigs par)
  -> par ⊢ s ~[ (makeIs (authSigs par)) ]~* s'
prop1 s s' par p1 p2 p3 p4 p5 p6 p7 p8  = prop s s' par
  (authSigs par) [] (authSigs par) refl refl p1 p2 p3 p4 p5 p6 p7 p8
\end{code}
}


\begin{code}[hide]



appendLemma x [] b = refl
appendLemma x (a ∷ as) b = cong (λ y → a ∷ y) (appendLemma x as b) 


∈lemma [] ys z = here refl
∈lemma (x ∷ xs) ys z = there (∈lemma xs ys z)


finalSigLemma pkh x [] = refl
finalSigLemma pkh x (y ∷ []) = refl
finalSigLemma pkh x (y ∷ z ∷ xs) = finalSigLemma pkh x (z ∷ xs)

--Generalized Prop1 (Can add signatures 1 by 1)
--Actual Prop1 (Can add all signatures 1 by 1)
 


--UniqueInsertLemma sub-lemmas
_⊆_ : List a -> List a -> Set
l1 ⊆ l2 = All (_∈ l2) l1

⊆-cons : (x : a){l1 l2 : List a} -> l1 ⊆ l2 -> l1 ⊆ (x ∷ l2)
⊆-cons x [] = []
⊆-cons x (px ∷ p) = there px ∷ ⊆-cons x p

⊆-refl : (l : List a) -> l ⊆ l
⊆-refl [] = []
⊆-refl (x ∷ l) = here refl ∷ ⊆-cons x (⊆-refl l)

⊆-trans : {l1 l2 l3 : List a} -> l1 ⊆ l2 -> l2 ⊆ l3 -> l1 ⊆ l3
⊆-trans [] p2 = []
⊆-trans (px ∷ p1) p2 = All.lookup p2 px ∷ ⊆-trans  p1 p2

insert-lem1 : (x : PubKeyHash)(l : List PubKeyHash) -> x ∈ insert x l
insert-lem1 x [] = here refl
insert-lem1 x (y ∷ l) with x == y in eq
... | false = there (insert-lem1 x l) 
... | true rewrite ==to≡ x y eq = here refl

insert-lem2 : (x y : PubKeyHash)(l : List PubKeyHash) -> x ∈ l -> x ∈ insert y l
insert-lem2 x y [] pf = there pf
insert-lem2 x y (z ∷ l) (here px) with y == z in eq
...| false rewrite px = here refl
...| true rewrite px = here refl
insert-lem2 x y (z ∷ l) (there pf) with y == z in eq
...| false = there (insert-lem2 x y l pf) 
...| true = there pf

del : ∀{x} (l : List a) -> x ∈ l -> List a
del (_ ∷ xs) (here px) = xs
del (x ∷ xs) (there p) = x ∷ del xs p

length-del : ∀{x}{l : List a} (p : x ∈ l) -> N.suc (length (del l p)) ≡ length l
length-del (here px) = refl
length-del (there p) = cong N.suc (length-del p) 

∈-del : ∀{x y}{l : List a} (p : x ∈ l) -> x ≢ y -> y ∈ l -> y ∈ del l p
∈-del (here refl) e (here refl) = ⊥-elim (e refl)
∈-del (there p)   e (here refl) = here refl
∈-del (here refl) e (there w) = w
∈-del (there p)   e (there w) = there (∈-del p e w) 

subset-del : ∀{x}{l1 l2 : List a} (p : x ∈ l2) -> (x ∉ l1) -> l1 ⊆ l2 -> l1 ⊆ del l2 p
subset-del p n [] = []
subset-del p n (px ∷ su) = ∈-del p (λ e -> n (here e)) px ∷ subset-del p (λ p → n (there p)) su

unique-lem : {l1 l2 : List a} -> l1 ⊆ l2
  -> Unique l1 -> length l2 N.≥ length l1
unique-lem [] root = N.z≤n
unique-lem (px ∷ sub) (x :: un)
  rewrite sym (length-del px) = N.s≤s (unique-lem (subset-del px x sub) un)

insertList-sublem : (l1 l2 : List PubKeyHash) (x : PubKeyHash)
  -> x ∈ l2 -> x ∈ insertList l1 l2
insertList-sublem [] l x pf = pf
insertList-sublem (y ∷ l1) l2 x pf = insertList-sublem l1 (insert y l2) x (insert-lem2 x y l2 pf)

insertList-lem : (l1 l2 : List PubKeyHash) -> l1 ⊆ insertList l1 l2
insertList-lem [] l = []
insertList-lem (x ∷ l1) l2 = insertList-sublem l1 (insert x l2) x
  (insert-lem1 x l2) ∷ insertList-lem l1 (insert x l2)

--Unique Insert Lemma
\end{code}

\newcommand\msUil{%
\begin{code}
uil : ∀ (l1 l2 : List PubKeyHash) (pf : Unique l1)
  -> (length (insertList l1 l2) N.≥ length l1)
\end{code}
}


\newcommand\msMSLemma{%
\begin{code}
lemmaMultiStep : ∀ (par : MParams) (s s' s'' : State) (is is' : List Redeemer)
                   -> par ⊢ s  ~[ is  ]~* s'
                   -> par ⊢ s' ~[ is' ]~* s''
                   -> par ⊢ s  ~[ is ++ is' ]~* s''
lemmaMultiStep par s .s s'' [] is' nil p2 = p2
lemmaMultiStep par s s' s'' (x ∷ is) is' (cons {s' = s'''} p1 p2) p3
  = cons p1 (lemmaMultiStep par s''' s' s'' is is' p2 p3)
\end{code}
}


\begin{code}[hide]


  
uil l1 l2 pf = unique-lem (insertList-lem l1 l2) pf
  
--Multi-Step lemma


--LiqLemma (Can add signatures 1 by 1 and then pay)
\end{code}

\newcommand\msLiqLem{%
\begin{code}
liqLemma : ∀ { v pkh d sigs tok } (s s' : State) (par : MParams)
          -> valid s -> validP par
          -> datum s ≡ (tok , Collecting v pkh d sigs)
          -> datum s' ≡ (tok , Holding)
          -> outVal s' ≡ v
          -> value s ≡ value s' + v
          -> tsig s' ≡ pkh
          -> par ⊢ s ~[ ((makeIs (authSigs par)) ++ [ Pay ]) ]~* s'
\end{code}
}

\newcommand\msLiqLemP{%
\begin{code}
liqLemma {v} {pkh} {d} {sigs} {tok}
  s1@record { datum = .(tok , Collecting oV sig d sigs) }
  s2@record { outVal = oV ; tsig = sig } par (Col p1 p2 p3 p4)
  (p5 , p6 , p7) refl refl refl refl refl
  = lemmaMultiStep par s1 s' s2 (makeIs (authSigs par)) [ Pay ]
    (prop1 s1 s' par refl refl refl refl refl refl refl refl)
    (cons (TPay (N.≤-trans p6 (uil (authSigs par) sigs p5))
    refl refl refl refl) nil)
  where
    s' = record
          { datum = tok , (Collecting oV sig d (insertList (authSigs par) sigs)) 
          ; value = s1 .value
          ; outVal = s1 .outVal 
          ; interval = s1 .interval 
          ; tsig = finalSig (tsig s1) (authSigs par)
          ; spends = s1 .spends
          ; threadTokCS = s1 .threadTokCS }
\end{code}
}


\newcommand\msRewrites{%
\begin{code}
rewriteValue : ∀ (a b : Value)
  -> (a + (negValue b)) + b ≡ a
rewriteValue a b rewrite assocVal a (negValue b) b
  | commVal (negValue b) b | v-v b | addValIdR a = refl
  
rewriteGeq : ∀ (a b : Value)
  -> geq a ((a + (negValue b)) + b) ≡ true
rewriteGeq a b rewrite rewriteValue a b = geq-refl a

rewriteValue' : ∀ (a b : Value)
  -> b + (a + (negValue b)) ≡ a
rewriteValue' a b rewrite commVal b (a + (negValue b))
  | rewriteValue a b  = refl
\end{code}
}


\begin{code}[hide]



                                                                             

--Liquidity (For any state that is valid and has valid parameters,
--there exists another state and some inputs such that we can transition
--there and have no value left in the contract)

\end{code}

\newcommand\msSfin{%
\begin{code}
sfin : State
sfin = record
             { datum = (0 , 0) , Holding
             ; value = emptyValue
             ; outVal = emptyValue
             ; interval = toPOSIXTime 0 , toPOSIXTime 0 
             ; tsig = 0
             ; spends = 0
             ; threadTokCS = 0 }
\end{code}
}


\newcommand\msLiquidityStatement{%
\begin{code}
liquidity : ∀ (par : MParams) (s : State)
          -> invariant s -> validP par
          -> ∃[ s' ] ∃[ is ] (par ⊢ s ~[ is ]~|* s')
\end{code}
}


\newcommand\msLiquidityProof{%
\begin{code}         
liquidity par s@record { datum = (tok , Holding) ; value = value }
  (Hol refl) p@(p2 , p3 , p4)
  with (lovelaces x2MinValue > lovelaces value) in eq
...| true = ⟨ sfin , ⟨ [ Stop ] , (fin nil (TStop refl eq)) ⟩ ⟩
...| false = ⟨ sfin , ⟨ (((Propose (value - minValue) 0 0) ∷
             ((makeIs (authSigs par)) ++ [ Pay ]) ++ [ Stop ])) ,
             fin {s' = s''} (cons (TPropose (rewriteGeq value minValue)
             (geqSub value minValue minValue (lovelaceLemma value
             (ltIntFalseToGeq (lovelaces value) (pos 6) eq)))
             refl refl refl (beforeLemma (maxWait par) p4))
             (liqLemma s' s'' par (Col refl (rewriteGeq value minValue) 
             (geqSub value minValue minValue (lovelaceLemma value
             (ltIntFalseToGeq (lovelaces value) (pos 6) eq))) root) p
             refl refl refl (sym (rewriteValue' value minValue)) refl))
             (TStop refl refl) ⟩ ⟩
\end{code}
}

\begin{code}[hide]



     where
       s'' = record
              { datum = tok , Holding
              ; value = minValue
              ; outVal = (value - minValue)
              ; interval = (toPOSIXTime 0) , (toPOSIXTime 0) 
              ; tsig = 0
              ; spends = 0
              ; threadTokCS = 0 }
       s' = record
             { datum = tok , (Collecting (value - minValue) 0 0 [])
             ; value = value
             ; outVal = s .outVal
             ; interval = toPOSIXTime (maxWait par) ,
                          toPOSIXTime (maxWait par + 100) 
             ; tsig = s .tsig
             ; spends = s .spends
             ; threadTokCS = s .threadTokCS }

\end{code}
\newcommand\msLiquidityProofTwo{%
\begin{code}         
liquidity par record { datum = (tok , Collecting v' pkh' d' sigs') ;
  value = value } (Col refl p2 p3 p4) p@(p7 , p8 , p9) =
\end{code}
}

\begin{code}[hide]

    ⟨ sfin , ⟨ ((Cancel ∷ (Propose (value - minValue) 0 0) ∷
    ((makeIs (authSigs par)) ++ [ Pay ])) ++ [ Stop ]) ,
    fin {s' = s'''} (cons {s' = s'} (TCancel (ltIntegerLemma d')
    refl refl refl) (cons (TPropose (rewriteGeq value minValue)
    (geqSub value minValue minValue
    (geqAddTrans value v' minValue minValue p2 p3)) refl refl refl
    (beforeLemma (maxWait par) p9))
    (liqLemma s'' s''' par (Col refl (rewriteGeq value minValue)
    (geqSub value minValue minValue
    (geqAddTrans value v' minValue minValue p2 p3)) root) p
    refl refl refl (sym (rewriteValue' value minValue)) refl)))
    (TStop refl refl) ⟩ ⟩ 
    where
      s''' = record
             { datum = tok , Holding
             ; value = minValue
             ; outVal = value - minValue
             ; interval = (toPOSIXTime 0) , (toPOSIXTime 0) 
             ; tsig = 0
             ; spends = 0
             ; threadTokCS = 0
             }
      s'' = record
            { datum = tok , (Collecting (value - minValue) 0 0 [])
            ; value = value
            ; outVal = 0
            ; interval = toPOSIXTime (maxWait par) , toPOSIXTime 0
            ; tsig = 0
            ; spends = 0
            ; threadTokCS = 0
            }
      s' = record
             { datum = tok , Holding
             ; value = value
             ; outVal = 0
             ; interval =  toPOSIXTime (d' + 1) , toPOSIXTime (d' + 100) 
             ; tsig = 0
             ; spends = 0
             ; threadTokCS = 0
             }


minValLiquidity : ∀ (par : MParams) (s : State)
          -> valid s -> validP par
          -> ∃[ s' ] ∃[ is ]
             ((par ⊢ s ~[ is ]~* s') ×
             ((lovelaces x2MinValue > lovelaces (value s')) ≡ true))
minValLiquidity par s@record { datum = (tok , Holding) ; value = value ; outVal = outVal ;
  interval = interval ; tsig = tsig ; spends = spends ; threadTokCS = threadTokCS }
  (Hol refl) p@(p2 , p3 , p4) with (lovelaces x2MinValue > lovelaces value) in eq
...| true = ⟨ s , ⟨ [] , (nil , eq) ⟩ ⟩ 
...| false = ⟨ s'' , ⟨ (((Propose (value - minValue) 0 0) ∷ ((makeIs (authSigs par)) ++ [ Pay ]))) ,
             (cons (TPropose (rewriteGeq value minValue)
             (geqSub value minValue minValue (lovelaceLemma value (ltIntFalseToGeq (lovelaces value) (pos 6) eq)))
             refl refl refl
             (beforeLemma (maxWait par) p4)) (liqLemma s' s'' par (Col refl (rewriteGeq value minValue) 
             (geqSub value minValue minValue (lovelaceLemma value (ltIntFalseToGeq (lovelaces value) (pos 6) eq))) root) p
             refl refl refl (sym (rewriteValue' value minValue)) refl) , refl ) ⟩ ⟩
     where
       s'' = record
              { datum = tok , Holding
              ; value = minValue
              ; outVal = (value - minValue)
              ; interval = interval
              ; tsig = 0
              ; spends = spends
              ; threadTokCS = threadTokCS
              }
       s' = record
             { datum = tok , (Collecting (value - minValue) 0 0 [])
             ; value = value
             ; outVal = outVal
             ; interval = toPOSIXTime (maxWait par) , toPOSIXTime (maxWait par + 100) 
             ; tsig = tsig
             ; spends = spends
             ; threadTokCS = threadTokCS
             }
minValLiquidity par record { datum = (tok , Collecting v' pkh' d' sigs') ; value = value ;
  outVal = outVal ; interval = interval ; tsig = tsig ; spends = spends ; threadTokCS = threadTokCS }
  (Col refl p2 p3 p4) p@(p7 , p8 , p9)
  = ⟨ s''' , ⟨ ((Cancel ∷ (Propose (value - minValue) 0 0) ∷ ((makeIs (authSigs par)) ++ [ Pay ]))) ,
             (cons {s' = s'} (TCancel (ltIntegerLemma d') refl refl refl) (cons
             (TPropose (rewriteGeq value minValue)
             (geqSub value minValue minValue (geqAddTrans value v' minValue minValue p2 p3)) refl refl refl
             (beforeLemma (maxWait par) p9)) (liqLemma s'' s''' par (Col refl (rewriteGeq value minValue)
             (geqSub value minValue minValue (geqAddTrans value v' minValue minValue p2 p3)) root) p
             refl refl refl (sym (rewriteValue' value minValue)) refl)) , refl) ⟩ ⟩ 
    where
      s''' = record
             { datum = tok , Holding
             ; value = minValue
             ; outVal = value - minValue
             ; interval = (toPOSIXTime 0) , (toPOSIXTime 0) 
             ; tsig = 0
             ; spends = 0
             ; threadTokCS = threadTokCS
             }
      s'' = record
            { datum = tok , (Collecting (value - minValue) 0 0 [])
            ; value = value
            ; outVal = 0
            ; interval =  toPOSIXTime (maxWait par) , toPOSIXTime 0
            ; tsig = tsig
            ; spends = 0
            ; threadTokCS = threadTokCS
            }
      s' = record
             { datum = tok , Holding
             ; value = value
             ; outVal = 0
             ; interval =  toPOSIXTime (d' + 1) , toPOSIXTime 0 
             ; tsig = tsig
             ; spends = 0
             ; threadTokCS = threadTokCS
             }

-- Extracting the State from ScriptContext

sig : ScriptContext -> PubKeyHash
sig = ScriptContext.signature

iRef : ScriptContext -> TxOutRef
iRef = ScriptContext.inputRef

-- Starting State for normal transitions
getS : Datum -> ScriptContext -> State
getS (tok , lab) ctx = record
              { datum = (tok , lab)
              ; value = oldValue ctx
              ; outVal = 0
              ; interval =  toPOSIXTime 0 , toPOSIXTime 0
              ; tsig = 0
              ; spends = 0
              ; threadTokCS = 0 }

-- Initial State when we mint the token and put the smart contract on the blockchain
getMintS : TokenName -> ScriptContext -> State
getMintS tn ctx = record
                { datum = newDatum ctx
                ; value = newValue ctx
                ; outVal = 0
                ; interval = validRange ctx
                ; tsig = sig ctx
                ; spends = iRef ctx
                ; threadTokCS = ownCurrencySymbol ctx }

-- Resulting State for normal transitions
\end{code}

\newcommand\msGetS{%
\begin{code}
getS' : Datum -> ScriptContext -> State
getS' (tok , Holding) ctx = record
             { datum = newDatum ctx
             ; value = newValue ctx
             ; outVal = 0
             ; interval = validRange ctx 
             ; tsig = sig ctx
             ; spends = iRef ctx
             ; threadTokCS = 0 }
getS' (tok , Collecting v pkh d sigs) ctx = record
             { datum = newDatum ctx
             ; value = newValue ctx
             ; outVal = getPayment pkh v ctx
             ; interval = validRange ctx
             ; tsig = sig ctx
             ; spends = iRef ctx
             ; threadTokCS = 0 }
\end{code}
}

\begin{code}[hide]


-- Getting the Model parameters from the parameters of the validator and minting policy
getPar : Params -> TxOutRef -> TokenName -> MParams
getPar p oref tn = record { uniqueId  = oref
                          ; threadTokName = tn
                          ; authSigs = authSigs p
                          ; minSigs = minSigs p
                          ; maxWait = maxWait p }

-- Lemma for validator returning true implies transition
elemTo∈ : ∀ {sig : PubKeyHash} {sigs : List PubKeyHash} -> (elem sig sigs) ≡ true -> sig ∈ sigs
elemTo∈ {sig} {x ∷ sigs} pf with orToSum (sig == x) (elem sig sigs) pf
... | inj₁ a = here (==to≡ sig x a)
... | inj₂ b = there (elemTo∈ b)

--Validator returning true implies that we can perform a transition
\end{code}

\newcommand\msVIR{%
\begin{code}
validatorImpliesRunning : ∀ {oref tn} (par : Params)
  (d : Datum) (i : Redeemer) (ctx : ScriptContext)
  -> getMintedAmount ctx ≡ 0
  -> (pf : agdaValidator par d i ctx ≡ true)
  -> (getPar par oref tn ⊢ getS d ctx ~[ i ]~> getS' d ctx
     × continuing ctx ≡ true
     × checkTokenIn (d .fst) ctx ≡ true
     × checkTokenOut (d .fst) ctx ≡ true)
\end{code}
}

\begin{code}[hide]



validatorImpliesRunning   par (tok , Holding) (Propose v pkh d) ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , Holding) ; continues = continues  } n pf = ⊥-elim (&&7false (checkTokenIn tok ctx) (eqValue outputVal inputVal) (geq inputVal (v + minValue)) (geq v minValue) (notTooLate par d ctx) continues (checkTokenOut tok ctx) pf)
validatorImpliesRunning par (tok , Holding) (Propose v pkh d) ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , Collecting v' pkh' d' sigs) ; continues = continues } n pf
  rewrite sym (==vto≡ v v' (get (go (checkTokenOut tok ctx) (go continues (go (notTooLate par d ctx) (go (geq v minValue) (go (geq inputVal (v + minValue)) (go (eqValue outputVal inputVal) (go (checkTokenIn tok ctx) pf))))))))) | 
  sym (==to≡ pkh pkh' (get (go (eqValue v v') (go (checkTokenOut tok ctx) (go continues (go (notTooLate par d ctx)(go (geq v minValue) (go (geq inputVal (v + minValue)) (go (eqValue outputVal inputVal) (go (checkTokenIn tok ctx) pf)))))))))) |
  sym (==ito≡ d d' (get (go (pkh == pkh') (go (eqValue v v') (go (checkTokenOut tok ctx) (go continues (go (notTooLate par d ctx) (go (geq v minValue) (go (geq inputVal (v + minValue)) (go (eqValue outputVal inputVal) (go (checkTokenIn tok ctx) pf))))))))))) |
  (==lto≡ sigs [] (get (go (d == d') (go (pkh == pkh') (go (eqValue v v') (go (checkTokenOut tok ctx) (go continues (go (notTooLate par d ctx) (go (geq v minValue) (go (geq inputVal (v + minValue)) (go (eqValue outputVal inputVal) (go (checkTokenIn tok ctx) pf)))))))))))) |
  sym (==tto≡ tok tok' (go (sigs == []) (go (d == d') (go (pkh == pkh') (go (eqValue v v') (go (checkTokenOut tok ctx) (go continues (go (notTooLate par d ctx) (go (geq v minValue) (go (geq inputVal (v + minValue)) (go (eqValue outputVal inputVal) (go (checkTokenIn tok ctx) pf))))))))))))
  = TPropose (get (go (eqValue outputVal inputVal) (go (checkTokenIn tok ctx) pf))) (get (go (geq inputVal (v + minValue)) (go (eqValue outputVal inputVal) (go (checkTokenIn tok ctx) pf)))) refl refl (==vto≡ outputVal inputVal (get (go (checkTokenIn tok ctx) pf))) (get (go (geq v minValue) (go (geq inputVal (v + minValue)) (go (eqValue outputVal inputVal) (go (checkTokenIn tok ctx) pf))))) , get (go (notTooLate par d ctx) (go (geq v minValue) (go (geq inputVal (v + minValue)) (go (eqValue outputVal inputVal) (go (checkTokenIn tok ctx) pf))))) , get pf , get (go continues (go (notTooLate par d ctx) (go (geq v minValue) (go (geq inputVal (v + minValue)) (go (eqValue outputVal inputVal) (go (checkTokenIn tok ctx) pf))))))

validatorImpliesRunning par (tok , Holding) (Add x) ctx n pf = ⊥-elim (&&false (checkTokenIn tok ctx) pf)
validatorImpliesRunning par (tok , Holding) Pay ctx n pf = ⊥-elim (&&false (checkTokenIn tok ctx) pf)
validatorImpliesRunning par (tok , Holding) Cancel ctx n pf = ⊥-elim (&&false (checkTokenIn tok ctx) pf)
validatorImpliesRunning par (tok , Holding) Stop ctx refl pf = ⊥-elim (&&3false (checkTokenIn tok ctx) (lovelaces x2MinValue > lovelaces (oldValue ctx)) (not (continuing ctx)) pf)
validatorImpliesRunning par (tok , Collecting v pkh d sigs) (Propose v' pkh' d') ctx n pf = ⊥-elim (&&false (checkTokenIn tok ctx) pf)
validatorImpliesRunning par (tok , Collecting v pkh d sigs) (Add pkh') ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , Holding) ; signature = signature ; continues = continues } n pf = ⊥-elim (&&5false (eqValue outputVal inputVal) (pkh' == signature) (elem pkh' (par .authSigs)) continues (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))
validatorImpliesRunning par (tok , Collecting v pkh d sigs) (Add sig) ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , Collecting v' pkh' d' sigs') ; signature = signature ; continues = continues } n pf
  rewrite sym (==vto≡ v v' (get (go (checkTokenOut tok ctx) (go continues (go (elem sig (authSigs par)) (go (sig == signature) (go (eqValue outputVal inputVal) (go (checkTokenIn tok ctx) pf)))))))) |
  sym (==to≡ pkh pkh' (get (go (eqValue v v') (go (checkTokenOut tok ctx) (go continues (go (elem sig (authSigs par)) (go (sig == signature) (go (eqValue outputVal inputVal) (go (checkTokenIn tok ctx) pf))))))))) |
  sym (==ito≡ d d' (get (go (pkh == pkh') (go (eqValue v v') (go (checkTokenOut tok ctx) (go continues (go (elem sig (authSigs par)) (go (sig == signature) (go (eqValue outputVal inputVal) (go (checkTokenIn tok ctx) pf)))))))))) |
  (==lto≡ sigs' (insert sig sigs) (get (go (d == d') (go (pkh == pkh') (go (eqValue v v') (go (checkTokenOut tok ctx) (go continues (go (elem sig (authSigs par)) (go (sig == signature) (go (eqValue outputVal inputVal) (go (checkTokenIn tok ctx) pf))))))))))) |
  sym (==tto≡ tok tok' (go (sigs' == (insert sig sigs)) (go (d == d') (go (pkh == pkh') (go (eqValue v v') (go (checkTokenOut tok ctx) (go continues (go (elem sig (authSigs par)) (go (sig == signature) (go (eqValue outputVal inputVal) (go (checkTokenIn tok ctx) pf)))))))))))
  = TAdd (elemTo∈ (get (go (sig == signature) (go (outputVal == inputVal) (go (checkTokenIn tok ctx) pf)))))
  (sym (==to≡ sig signature (get (go (outputVal == inputVal) (go (checkTokenIn tok ctx) pf))))) refl refl (==vto≡ outputVal inputVal (get (go (checkTokenIn tok ctx) pf))) ,
  get (go (elem sig (authSigs par)) (go (sig == signature) (go (outputVal == inputVal) (go (checkTokenIn tok ctx) pf)))) , get pf ,
  get (go continues (go (elem sig (authSigs par)) (go (sig == signature) (go (outputVal == inputVal) (go (checkTokenIn tok ctx) pf)))))

validatorImpliesRunning par (tok , Collecting v pkh d sigs) Pay ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , Holding) ; signature = signature ; continues = continues } n pf rewrite 
  sym (==tto≡ tok tok' (go ((outputVal + v) == inputVal) (go (checkPayment pkh v ctx)
  (go (checkTokenOut tok ctx) (go continues (go ((lengthNat sigs) >= (minSigs par)) (go (checkTokenIn tok ctx) pf)))))))
  = (TPay (lengthNatToLength (minSigs par) sigs (get (go (checkTokenIn tok ctx) pf))) refl refl
  (==vto≡ (outputVal + v) inputVal (get (go (checkPayment pkh v ctx)
  (go (checkTokenOut tok ctx) (go continues (go ((lengthNat sigs) >= (minSigs par)) (go (checkTokenIn tok ctx) pf)))))))
  (==vto≡ (getPayment pkh v ctx) v (get (go (checkTokenOut tok ctx) (go continues (go ((lengthNat sigs) >= (minSigs par)) (go (checkTokenIn tok ctx) pf))))))) ,
  get (go ((lengthNat sigs) >= (minSigs par)) (go (checkTokenIn tok ctx) pf)) , get pf , get (go continues (go ((lengthNat sigs) >= (minSigs par)) (go (checkTokenIn tok ctx) pf)))
validatorImpliesRunning par (tok , Collecting v pkh d sigs) Pay ctx@record { outputDatum = (tok' , Collecting v' pkh' d' sigs') ; continues = continues } n pf = ⊥-elim (&&3false ((lengthNat sigs) >= (par .minSigs)) continues (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))

validatorImpliesRunning par (tok , Collecting v pkh d sigs) Cancel ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , Holding) ; payments = payments ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = mint ; tokCurrSymbol = tokCurrSymbol ; validInterval = validInterval } n pf rewrite sym ( ==tto≡ tok tok' (go (expired d ctx) (go (checkTokenOut tok ctx) (go continues (go (outputVal == inputVal) (go (checkTokenIn tok ctx) pf))))))
  = TCancel (get (go (checkTokenOut tok ctx) (go continues (go (outputVal == inputVal) (go (checkTokenIn tok ctx) pf))))) refl refl (==vto≡ outputVal inputVal (get (go (checkTokenIn tok ctx) pf))) ,
  get (go (outputVal == inputVal) (go (checkTokenIn tok ctx) pf)) , get pf , get (go continues (go (outputVal == inputVal) (go (checkTokenIn tok ctx) pf)))
validatorImpliesRunning par (tok , Collecting v pkh d sigs) Cancel ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , Collecting v' pkh' d' sigs') ; continues = continues } n pf = ⊥-elim (⊥-elim (&&3false (outputVal == inputVal) continues (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))
validatorImpliesRunning par (tok , Collecting v pkh d sigs) Stop ctx n pf = ⊥-elim (&&false (checkTokenIn tok ctx) pf)



-- Minting the token implies we are in the initial state of our model
mintingImpliesInitial : ∀ (par : Params) (adr : Address) (oref : TxOutRef) (tn : TokenName) (ctx : ScriptContext)
                           -> getMintedAmount ctx ≡ 1
                           -> (pf : agdaPolicy par adr oref tn tt ctx ≡ true)
                           -> (getPar par oref tn ⊢ getMintS tn ctx
                              × continuing ctx ≡ true
                              × getMintedAmount ctx ≡ 1
                              × checkTokenOut (ownAssetClass tn ctx) ctx ≡ true)
mintingImpliesInitial par adr oref tn ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , Holding) ; payments = _ ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = .1 ; tokCurrSymbol = cs ; validInterval = _ } refl pf
  rewrite sym (==tto≡ (cs , tn) tok (get (go (oref == inputRef) (go continues pf))))
  = TStart refl (get (get (go ((cs , tn) == tok) (go (oref == inputRef) (go continues pf)))))
    (==to≡ oref inputRef (get (go continues pf))) (get (go (checkValue adr tn ctx)
    (go (checkDatum adr tn ctx) (go (consumes oref ctx) (go continues pf)))))
    (get (go (noDups (par .authSigs)) (go (checkValue adr tn ctx) (go (checkDatum adr tn ctx)
    (go (consumes oref ctx) (go continues pf))))))
    (go (lengthNat (par .authSigs) >= (par .minSigs)) (go (noDups (par .authSigs))
    (go (checkValue adr tn ctx) (go (checkDatum adr tn ctx) (go (consumes oref ctx) (go continues pf)))))) , (get pf , refl) ,
    go (geq outputVal x2MinValue ) (get (go ((cs , tn) == tok) (go (oref == inputRef) (go continues pf)))) 

mintingImpliesInitial par adr oref tn record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , Collecting x x₁ x₂ x₃) ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = .1  } refl pf = ⊥-elim (&&2false continues (eqNat oref inputRef) pf)

-- Validator returning true and burning a token implies we are in the terminal state 
bothImplyFinal : ∀ (par : Params) (d : Datum) (adr : Address) (oref : TxOutRef)
  (tn : TokenName) (i : Redeemer) (ctx : ScriptContext)
  -> getMintedAmount ctx ≡ -1
  -> (agdaValidator par d i ctx && agdaPolicy par adr oref tn tt ctx) ≡ true
  -> (getPar par oref tn ⊢ getS d ctx ~[ i ]~| getS' d ctx
     × continuing ctx ≡ false
     × getMintedAmount ctx ≡ -1
     × checkTokenIn (d .fst) ctx ≡ true)

bothImplyFinal par (tok , Holding) adr oref tn (Propose v pkh d) ctx@record { inputVal = inputVal ; outputVal = outputVal ; continues = false } refl p2 = ⊥-elim (get⊥ (sym (go (notTooLate par d ctx) (go (geq v minValue) (go (geq inputVal (v + minValue)) (go (outputVal == inputVal) (go (checkTokenIn tok ctx) (get p2))))))))
bothImplyFinal par dat@(tok , Holding) adr oref tn i@(Propose v pkh d) ctx@record { continues = true } refl p2 = ⊥-elim (get⊥ (sym (go (agdaValidator par dat i ctx) p2)))
bothImplyFinal par (tok , Holding) adr oref tn (Add sig) ctx refl p2 = ⊥-elim (&&false (checkTokenIn tok ctx) (get p2))
bothImplyFinal par (tok , Holding) adr oref tn Pay ctx refl p2 = ⊥-elim (&&false (checkTokenIn tok ctx) (get p2))
bothImplyFinal par (tok , Holding) adr oref tn Cancel ctx refl p2 = ⊥-elim (&&false (checkTokenIn tok ctx) (get p2))
bothImplyFinal par dat@(tok , Holding) adr oref tn Stop ctx refl p2 = (TStop refl (get (go (checkTokenIn tok ctx) (get p2)))) , unNot (go (agdaValidator par dat Stop ctx) p2) , refl , get (get p2)
bothImplyFinal par (tok , Collecting pkh v d sigs) adr oref tn (Propose v' pkh' d') ctx refl p2 = ⊥-elim (&&false (checkTokenIn tok ctx) (get p2))
bothImplyFinal par (tok , Collecting pkh v d sigs) adr oref tn (Add sig) ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = false } refl p2 = ⊥-elim (get⊥ (sym (go (elem sig (par .authSigs)) (go (sig == signature) (go (outputVal == inputVal) (go (checkTokenIn tok ctx) (get p2)))))))
bothImplyFinal par dat@(tok , Collecting pkh v d sigs) adr oref tn i@(Add sig) ctx@record { continues = true } refl p2 = ⊥-elim (get⊥ (sym (go (agdaValidator par dat i ctx) p2)))
bothImplyFinal par (tok , Collecting pkh v d sigs) adr oref tn Pay ctx@record { continues = false } refl p2 = ⊥-elim (get⊥ (sym (go ((lengthNat sigs) >= (minSigs par)) (go (checkTokenIn tok ctx) (get p2)))))
bothImplyFinal par dat@(tok , Collecting pkh v d sigs) adr oref tn Pay ctx@record { continues = true } refl p2 = ⊥-elim (get⊥ (sym (go (agdaValidator par dat Pay ctx) p2)))
bothImplyFinal par (tok , Collecting pkh v d sigs) adr oref tn Cancel ctx@record { inputVal = inputVal ; outputVal = outputVal ; continues = false } refl p2 = ⊥-elim (get⊥ (sym (go (outputVal == inputVal) (go (checkTokenIn tok ctx) (get p2)))))
bothImplyFinal par dat@(tok , Collecting pkh v d sigs) adr oref tn Cancel ctx@record { continues = true } refl p2 = ⊥-elim (get⊥ (sym (go (agdaValidator par dat Cancel ctx) p2)))
bothImplyFinal par (tok , Collecting pkh v d sigs) adr oref tn Stop ctx p1 p2 = ⊥-elim (&&false (checkTokenIn tok ctx) (get p2))


--Lemma for transition implies validation returns true
∈toElem : ∀ {sig : PubKeyHash} {sigs : List PubKeyHash}
  -> sig ∈ sigs -> (elem sig sigs) ≡ true
∈toElem {sig} (here refl) rewrite n=n sig = refl
∈toElem (there pf) rewrite ∈toElem pf = ||true

-- Performing a transition implies that the validator returns true
runningImpliesValidator : ∀ {oref tn} (par : Params) (d : Datum)
  (i : Redeemer) (ctx : ScriptContext)
  -> (getPar par oref tn ⊢ getS d ctx ~[ i ]~> getS' d ctx
     × continuing ctx ≡ true
     × checkTokenIn (d .fst) ctx ≡ true
     × checkTokenOut (d .fst) ctx ≡ true)
  -> agdaValidator par d i ctx ≡ true
runningImpliesValidator par (tok , Holding) i ctx
  (TPropose {v} {pkh} {d} p1 p2 refl refl refl p6 , refl , p8 , p9)
  rewrite v=v (oldValue ctx) | v=v v | n=n pkh | i=i d | t=t tok
    | p1 | p2 | p6 | p8 | p9 = refl
runningImpliesValidator par (tok , Collecting v pkh d sigs) i ctx
  (TAdd {sig} p1 refl refl refl refl , refl , p7 , p8)
  rewrite v=v (oldValue ctx) | v=v v | n=n pkh | i=i d | t=t tok
    | l=l (insert sig sigs) | n=n sig | ∈toElem p1 | p7 | p8 = p8 
runningImpliesValidator par (tok , Collecting v pkh d sigs) i ctx
  (TPay p1 refl refl refl p5 , refl , p7 , p8)
  rewrite p5 | v=v v | v=v ((newValue ctx) + v) | t=t tok
    | lengthToLengthNat (minSigs par) sigs p1 | p7 | p8 = refl
runningImpliesValidator par (tok , Collecting v pkh d sigs) i ctx
  (TCancel p1 refl refl refl , refl , p6 , p7)
  rewrite v=v (oldValue ctx) | t=t tok | p1 | p6 | p7 = refl

-- Being in the initial model state implies we can mint a token
initialImpliesMinting : ∀ (par : Params) (adr : Address) (oref : TxOutRef)
  (tn : TokenName) (top : ⊤) (ctx : ScriptContext)
  -> (getPar par oref tn ⊢ getMintS tn ctx
     × continuing ctx ≡ true
     × getMintedAmount ctx ≡ 1
     × checkTokenOut (ownAssetClass tn ctx) ctx ≡ true)
  -> agdaPolicy par adr oref tn top ctx ≡ true
initialImpliesMinting par adr oref tn top record { outputDatum = ((cs , tn) , Holding) }
  (TStart refl p2 refl p4 p5 p6 , refl , refl , p9)
  rewrite n=n oref | t=t (cs , tn) | p2 | p4 | p5 | p6 | p9 = refl

-- Getting to the terminal state implies that the validator returns true and a token can be burned
stopImpliesBoth : ∀ (par : Params) (d : Datum) (adr : Address) (oref : TxOutRef)
  (tn : TokenName) (top : ⊤) (i : Redeemer) (ctx : ScriptContext)
  -> (getPar par oref tn ⊢ getS d ctx ~[ i ]~| getS' d ctx
     × continuing ctx ≡ false
     × getMintedAmount ctx ≡ -1
     × checkTokenIn (d .fst) ctx ≡ true)
  -> (agdaValidator par d i ctx &&
     agdaPolicy par adr oref tn top ctx) ≡ true
stopImpliesBoth par d adr oref tn top i ctx (TStop refl p2 , refl , refl , p5 )
  rewrite p2 | p5 = refl

finalImpliesBoth : ∀ {tn i} (par : Params) (d : Datum) (adr : Address)
  (oref : TxOutRef) (ctx : ScriptContext)
  -> (getPar par oref tn ⊢ getS d ctx ~[ i ]~| getS' d ctx
     × continuing ctx ≡ false
     × getMintedAmount ctx ≡ -1
     × checkTokenIn (d .fst) ctx ≡ true)
  -> (agdaValidator par d i ctx && agdaPolicy par adr oref tn tt ctx) ≡ true
finalImpliesBoth par d adr oref ctx (TStop refl p2 , refl , refl , p5 )
  rewrite p2 | p5 = refl


-- Defining the components for the equivalence relation between the model and the validator.

data Phase : Set where
  Initial  : Phase
  Running  : Phase
  Final    : Phase

\end{code}

\newcommand\msArgument{%
\begin{code}
record Argument : Set where
  field
    par  : Params
    adr  : Address
    oref : TxOutRef
    tn   : TokenName
    dat  : Datum
    red  : Redeemer
    ctx  : ScriptContext 
open Argument
\end{code}
}

\begin{code}[hide]


-- The equivalence relation
record _≈_ {A : Set} (f : A -> Bool) (R : A -> Set) : Set where
  field to   : ∀ {a} -> f a ≡ true -> R a
        from : ∀ {a} -> R a        -> f a ≡ true

-- If we mint exactly 1 token we are in the Initial Phase
-- If we burn a token and the input is Close, we are in the Terminal Phase
-- Otherwise we are in the Running Phase
classifier : Argument -> Phase
classifier record { ctx = record { mint = pos 1 } } = Initial
classifier record { ctx = record { mint = pos zero } } = Running
classifier _ = Final

-- The Validator as a function returning a boolean
totalF : Argument -> Bool
totalF arg with classifier arg
... | Initial  = agdaPolicy (arg .par) (arg .adr) (arg .oref) (arg .tn) tt (arg .ctx)
... | Running  = agdaValidator (arg .par) (arg .dat) (arg .red) (arg .ctx) 
... | Final = agdaValidator (arg .par) (arg .dat) (arg .red) (arg .ctx) &&
                 agdaPolicy (arg .par) (arg .adr) (arg .oref) (arg .tn) tt (arg .ctx)

-- The State Transition System as a relation
totalR : Argument -> Set
totalR arg with classifier arg
... | Initial = getPar (arg .par) (arg .oref) (arg .tn) ⊢ getMintS (arg .tn) (arg .ctx)
                × continuing (arg .ctx) ≡ true
                × getMintedAmount (arg .ctx) ≡ 1
                × checkTokenOutAddr (arg .adr) (ownAssetClass (arg .tn) (arg .ctx)) (arg .ctx) ≡ true

... | Running = getPar (arg .par) (arg .oref) (arg .tn)
                ⊢ getS (arg .dat) (arg .ctx) ~[ (arg .red) ]~> getS' (arg .dat) (arg .ctx)
                × continuing (arg .ctx) ≡ true
                × checkTokenIn (arg .dat .fst) (arg .ctx) ≡ true
                × checkTokenOut (arg .dat .fst) (arg .ctx) ≡ true
                
... | Final = getPar (arg .par) (arg .oref) (arg .tn)
                 ⊢ getS (arg .dat) (arg .ctx)  ~[ (arg .red) ]~| getS' (arg .dat) (arg .ctx)
                 × continuing (arg .ctx) ≡ false
                 × getMintedAmount (arg .ctx) ≡ -1
                 × checkTokenIn (arg .dat .fst) (arg .ctx) ≡ true



-- The equivalence proof


totalEquiv : totalF ≈ totalR
totalEquiv = record
  { to = λ { { arg@record { par = par ; dat = dat ; red = red ; ctx =
               ctx@record { mint = pos zero } } } pf
               → validatorImpliesRunning par dat red ctx refl pf ;
             { arg@record { par = par ; adr = adr ; oref = oref ; tn = tn ;
               ctx = ctx@record { mint = pos 1 } } } pf
               → mintingImpliesInitial par adr oref tn ctx refl pf ;
             { arg@record { par = par ; dat = dat ; red = red ; ctx =
               ctx@record { mint = pos (suc (suc n)) } } } pf
               → ⊥-elim (&&false (agdaValidator par dat red ctx) pf) ;
             { arg@record { par = par ; dat = dat ; adr = adr;
               oref = oref; red = red ; tn = tn ; ctx =
               ctx@record { mint = (negsuc zero) } } } pf
               → bothImplyFinal par dat adr oref tn red ctx refl pf ;
             { arg@record { par = par ; dat = dat ; red = red ; ctx =
               ctx@record { mint = (negsuc (N.suc n)) } } } pf
               → ⊥-elim (&&false (agdaValidator par dat red ctx) pf) }
  ; from = λ { { arg@record { par = par ; dat = dat ; red = red ; ctx =
                 ctx@record { mint = pos zero } } } pf
                 → runningImpliesValidator par dat red ctx pf ;
               { arg@record { par = par ; adr = adr ; oref = oref ;
                 tn = tn ; ctx = ctx@record { mint = pos 1 } } } pf
                 → initialImpliesMinting par adr oref tn tt ctx pf ;
               { arg@record { ctx = ctx@record { mint = pos (suc (suc n)) } } }
                 (p1 , p2 , () , p4) ;
               { arg@record { par = par ; adr = adr ; oref = oref ; dat = dat ;
                 ctx = ctx@record { mint = (negsuc zero) } } } pf
                 → finalImpliesBoth par dat adr oref ctx pf ;
               { arg@record { ctx = ctx@record { mint = (negsuc (N.suc n)) } } }
                 (p1 , p2 , () , p4) } }


-- Proof that several components (outVal, interval, tsig, spends, mint, token) of the starting state are irrelevant to the state transition and can be replaced with anything
inputRewrite : ∀ {oV t sig spn tok} (par : MParams) (s s' : State) (i : Redeemer)
                 -> par ⊢ s ~[ i ]~> s'
                 -> par ⊢ record
                           { datum = s .datum
                           ; value = s .value
                           ; outVal = oV
                           ; interval = t
                           ; tsig = sig
                           ; spends = spn
                           ; threadTokCS = tok
                           } ~[ i ]~> s'
inputRewrite par s s' (Propose v pkh d) (TPropose x x₁ x₂ x₃ x₄ x₅) = TPropose x x₁ x₂ x₃ x₄ x₅
inputRewrite par s s' (Add pkh) (TAdd x x₁ x₂ x₃ x₄) = TAdd x x₁ x₂ x₃ x₄
inputRewrite par s s' Pay (TPay x x₁ x₂ x₃ x₄) = TPay x x₁ x₂ x₃ x₄
inputRewrite par s s' Cancel (TCancel x x₁ x₂ x₃) = TCancel x x₁ x₂ x₃


\end{code}

\newcommand\msAuthCanSign{%
\begin{code}
onlyAuthorizedCanSign : ∀ (par : MParams) (s s' : State) (pkh : PubKeyHash)
  -> pkh ∉ par .authSigs
  -> ¬ (par ⊢ s ~[ Add pkh ]~> s')
onlyAuthorizedCanSign par s s' pkh pf (TAdd p1 p2 p3 p4 p5) = pf p1
\end{code}
}

\begin{code}[hide]


\end{code}


\newcommand\msDF{%
\begin{code}
deadlockFreedom : ∀ (s : State) (par : MParams)
          -> valid s -> validP par
          -> ∃[ s' ] ∃[ i ] ((par ⊢ s ~[ i ]~> s') ⊎ (par ⊢ s ~[ i ]~| s'))
\end{code}
}

\newcommand\msDFp{%
\begin{code}
deadlockFreedom record { datum = (tok , Holding) ; value = value} par p1 p2 with (lovelaces x2MinValue > lovelaces value) in eq
...| true = ⟨ s1 , ⟨ Stop , (inj₂ (TStop refl eq)) ⟩ ⟩
  where
  s1 = record
        { datum = (0 , 0) , Collecting 0 0 0 []
        ; value = unMap []
        ; outVal = unMap []
        ; interval = (toPOSIXTime 0) , (toPOSIXTime 0)
        ; tsig = 0
        ; spends = 0
        ; threadTokCS = 0
        } 
...| false = ⟨ s2 , ⟨ (Propose (value - minValue) 1234 0)  , inj₁ (TPropose (rewriteGeq value minValue) (geqSub value minValue minValue (lovelaceLemma value (ltIntFalseToGeq (lovelaces value) (pos 6) eq))) refl refl refl (beforeLemma (maxWait par) (_×_×_.thd3 p2))) ⟩ ⟩
  where
  s2 = record
        { datum = tok , Collecting (value - minValue) 1234 0 []
        ; value = value
        ; outVal = unMap []
        ; interval = (toPOSIXTime (maxWait par)) , (toPOSIXTime (maxWait par + 100))
        ; tsig = 0
        ; spends = 0
        ; threadTokCS = 0
        } 
deadlockFreedom s@record { datum = (tok , Collecting v pkh d sigs) } par p1 p2 = ⟨ s2 , ⟨ Cancel , (inj₁ (TCancel (ltIntegerLemma d) refl refl refl)) ⟩ ⟩
  where
  s2 = record
        { datum = tok , Holding
        ; value = s .value
        ; outVal = unMap []
        ; interval = (toPOSIXTime (d + 1)) , (toPOSIXTime (d + 100))
        ; tsig = 0
        ; spends = 0
        ; threadTokCS = 0
        } 

\end{code}
}

