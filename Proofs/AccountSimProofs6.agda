open import Validators.AccountSim6
open import Lib
open import Value hiding (addValue; subValue)

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

open import ProofLib

module Proofs.AccountSimProofs6 where

-- Model and proofs for the Account Simulation contract
  
-- The States of the State Transition System

record State : Set where
  field
    datum      : Datum
    value      : Value  
    tsig       : PubKeyHash
    spends     : TxOutRef
    token      : AssetClass
open State

-- Extra definitions necessary for the model

accMap : State -> AccMap
accMap s = s .datum .snd

sumVal : AccMap -> Value
sumVal [] = emptyValue
sumVal ((k , v) ∷ xs) = v + sumVal xs

internalVal : State -> Value
internalVal s = sumVal (accMap s) + minValue + assetClassValue (s .datum .fst) 1

iVal : AccMap -> AssetClass -> Value
iVal [] ac = minValue + assetClassValue ac 1
iVal ((k , v) ∷ xs) ac = v + (iVal xs) ac

internalVal' : State -> Value
internalVal' s = iVal (accMap s) (s .datum .fst)

iVal≡' : ∀ (map : AccMap) (ac : AssetClass)
  -> sumVal map + minValue + assetClassValue ac 1 ≡ iVal map ac
iVal≡' [] ac = refl
iVal≡' (x ∷ map) ac rewrite assocVal (x .snd) (sumVal map) minValue
  | assocVal (x .snd) (sumVal map + minValue) (assetClassValue ac 1)
  = cong (λ y → (x .snd) + y) (iVal≡' map ac)
  
iVal≡ : ∀ (s : State) -> internalVal s ≡ internalVal' s
iVal≡ s = iVal≡' (s .datum .snd) (s .datum .fst)


-- Model parameters consisting of the combined parameters of the validator and minting policy

record MParams : Set where
    field
       -- validatorAddress : Address
        uniqueId         : TxOutRef
        threadTokName    : TokenName
open MParams public

--Transition Rules

--The Initial Transition

data _⊢_ : MParams -> State -> Set where

  TStart : ∀ {par s}
    -> datum s ≡ ( token s , [] )
    -> spends s ≡ uniqueId par 
    -> token s .snd ≡ threadTokName par
    -> value s ≡ minValue + assetClassValue (token s) 1
    -------------------
    -> par ⊢ s

-- The Running Transition

data _⊢_~[_]~>_ : MParams -> State -> Redeemer -> State -> Set where
 
  TOpen : ∀ {par pkh s s' tok map}
    -> datum s ≡ (tok , map)
    -> tsig s' ≡ pkh 
    -> lookup pkh map ≡ Nothing
    -> datum s' ≡ (tok ,  insert pkh emptyValue map)
    -> value s' ≡ value s 
    -------------------
    -> par ⊢ s ~[ (Open pkh) ]~> s'

  TClose : ∀ {par pkh s s' tok map}
    -> datum s ≡ (tok , map)
    -> tsig s' ≡ pkh
    -> lookup pkh map ≡ Just emptyValue
    -> datum s' ≡ (tok , delete pkh map)
    -> value s' ≡ value s
    -------------------
    -> par ⊢ s ~[ (Close pkh) ]~> s'
    
  TDeposit : ∀ {par pkh val s s' v tok map}
    -> datum s ≡ (tok , map)
    -> tsig s' ≡ pkh
    -> lookup pkh map ≡ Just v
    -> geq val emptyValue ≡ true
    -> datum s' ≡ (tok , (insert pkh (v + val) map))
    -> value s' ≡ (value s) + val
    -------------------
    -> par ⊢  s ~[ (Deposit pkh val) ]~> s'
    
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

-- The Final Transition

data _⊢_~[_]~> : MParams -> State -> Redeemer -> Set where

  TStop : ∀ {par s}
    -> snd (datum s) ≡ []
    -------------------
    -> par ⊢ s ~[ Stop ]~>


--Multi-Step Transition

data _⊢_~[_]~*_ : MParams -> State -> List Redeemer -> State -> Set where

  nil : ∀ { par s }
    ----------------------
    -> par ⊢ s ~[ [] ]~* s

  cons : ∀ { par s s' s'' i is }
    -> par ⊢ s ~[ i ]~> s'
    -> par ⊢ s' ~[ is ]~* s''
    -------------------------
    -> par ⊢ s ~[ (i ∷ is) ]~* s''


data _⊢_~[_]~>* : MParams -> State -> List Redeemer -> Set where

  fin : ∀ { par s s' is i }
    -> par ⊢ s ~[ is ]~* s'
    -> par ⊢ s' ~[ i ]~>
    ---------------------------------
    -> par ⊢ s ~[ (is ++ [ i ]) ]~>*

 
-- Validity predicate

valid : State -> Set 
valid s = All (\y -> geq (snd y) emptyValue ≡ true) (accMap s)

-- Lemmas for Validity

lem : ∀ {pkh} (map : AccMap) (v : Value)
      -> geq v emptyValue ≡ true 
      -> All (λ y → geq (snd y) emptyValue ≡ true) map
      -> All (λ y → geq (snd y) emptyValue ≡ true) (insert pkh v map)

lem {pkh} [] v' p1 p2 = allCons {{p1}} 
lem {pkh} ((pkh' , v) ∷ map) v' p1 (allCons {{i}} {{is}}) with pkh == pkh'
...| true = allCons {{p1}} 
...| false = allCons {{i}} {{lem map v' p1 is}}

delem : ∀ {pkh} (map : AccMap)
      -> All (λ y → geq (snd y) emptyValue ≡ true) map
      -> All (λ y → geq (snd y) emptyValue ≡ true) (delete pkh map)
      
delem {pkh} [] p1 = p1
delem {pkh} ((pkh' , v') ∷ map) (allCons {{i}} {{is}}) with pkh == pkh'
...| true = is 
...| false = allCons {{i}} {{delem map is}}

geqLem : ∀ {pkh} (map : AccMap) (v : Value)
      -> All (λ y → geq (snd y) emptyValue ≡ true) map
      -> lookup pkh map ≡ Just v
      -> geq v emptyValue ≡ true
      
geqLem {pkh} ((pkh' , v') ∷ map) v allCons p2 with pkh == pkh'
geqLem {pkh} ((pkh' , v') ∷ map) v' (allCons {{i}} {{is}}) refl | true = i
geqLem {pkh} ((pkh' , v') ∷ map) v (allCons {{i}} {{is}}) p2 | false
       = geqLem map v is p2

-- Validity Proof

initialValidity : ∀ {s par}
  -> par ⊢ s
  -> valid s 
initialValidity {record { datum = .(_ , [])}}
                (TStart refl p2 p3 p4) = allNil

validity : ∀ {s s' i par}
  -> valid s
  -> par ⊢ s ~[ i ]~> s'
  -> valid s'
  
validity {record { datum = tok , map }}
         {record { datum = .(_ , insert _ emptyValue map) }} p
         (TOpen refl p2 p3 refl p5)
         = (lem map emptyValue refl p)
         
validity {record { datum = tok , map }}
         {record { datum = .(_ , delete _ map) }} p
         (TClose refl p2 p3 refl p5) = (delem map p)
      
validity {record { datum = tok , map }}
         {record { datum = .(_ , insert _ (v + val) map) }} p
         (TDeposit {val = val} {v = v} refl p2 p3 p4 refl p6)
         = lem map (v + val)
           (sumLemma v val (geqLem map v p p3) p4) p
         
validity {record { datum = tok , map }}
         {record { datum = .(_ , insert _ (v - val) map) }} p
         (TWithdraw {val = val} {v = v} refl p2 p3 p4 p5 refl refl)
         = (lem map (v - val) (diffLemma v val p5) p)
         
validity {record { datum = tok , map }}
         {record { datum = .(_ , insert from (vF - val)
                                (insert to (vT + val) map)) }} p
         (TTransfer {par} {from} {to} {val} {vF = vF} {vT = vT}
                    refl p2 p3 p4 p5 p6 p7 refl p9)
         = lem (insert to (vT + val) map) (vF - val) (diffLemma vF val p6)
           (lem map (vT + val) (sumLemma vT val (geqLem map vT p p4) p5) p)



-- Fidelity predicate

fides : State -> Set
fides s = value s ≡ internalVal s

-- Lemmas for Fidelity

maybe⊥ : ∀ {x : Value} -> Nothing ≡ Just x -> ⊥
maybe⊥ ()

maybe≡ : ∀ {a b : Value} -> Just a ≡ Just b → a ≡ b
maybe≡ refl = refl


iValLemma1 : ∀ {pkh} (map : AccMap) (ac : AssetClass)
           -> lookup pkh map ≡ Nothing
           -> iVal map ac ≡ iVal (insert pkh emptyValue map) ac


iValLemma1 {pkh} [] ac p = refl
iValLemma1 {pkh} (x ∷ map) ac p with pkh == (fst x)
...| false = cong (λ a → (x .snd) + a) (iValLemma1 map ac p)
...| true = ⊥-elim (maybe⊥ (sym p))


iValLemma2 : ∀ {pkh} (map : AccMap) (ac : AssetClass)
           -> lookup pkh map ≡ Just emptyValue
           -> iVal map ac ≡ iVal (delete pkh map) ac
           
iValLemma2 [] ac p = refl
iValLemma2 {pkh} (x ∷ map) ac p with pkh == (fst x)
...| false = cong (λ a → (x .snd) + a) (iValLemma2 map ac p)
...| true rewrite maybe≡ p = addValIdL (iVal map ac)


iValLemma3 : ∀ {pkh v val} (map : AccMap) (ac : AssetClass)
           -> lookup pkh map ≡ Just v
           -> (iVal map ac) + val ≡
              iVal (insert pkh (v + val) map) ac


iValLemma3 [] ac p = ⊥-elim (maybe⊥ p) 
iValLemma3 {pkh} {v} {val} (x ∷ map) ac p with pkh == (fst x)
...| false rewrite (assocVal (snd x) (iVal map ac) val)
     = cong (λ a → (snd x) + a) (iValLemma3 map ac p)
...| true rewrite maybe≡ p | assocVal v (iVal map ac) val
                | commVal (iVal map ac) val
                | assocVal v val (iVal map ac) = refl
                    

iValLemma4 : ∀ {from to vF vT val} (map : AccMap) (ac : AssetClass)
           -> lookup from map ≡ Just vF
           -> lookup to map ≡ Just vT
           -> from ≢ to
           -> iVal map ac ≡ iVal (insert from (vF - val)
                           (insert to (vT + val) map)) ac

iValLemma4 {from} {to} {vF} {vT} {val} (x ∷ map) ac p1 p2 p3 with to == (fst x) in eq1
iValLemma4 {from} {to} {vF} {vT} {val} (x ∷ map) ac p1 p2 p3 | true with from == to in eq2
iValLemma4 {from} {to} {vF} {vT} {val} (x ∷ map) ac p1 p2 p3 | true | true = ⊥-elim (p3 (==to≡ from to eq2))
iValLemma4 {from} {to} {vF} {vT} {val} (x ∷ map) ac p1 p2 p3 | true | false with from == (fst x) in eq3
iValLemma4 {from} {to} {vF} {vT} {val} (x ∷ map) ac p1 p2 p3 | true | false | true 
         rewrite ==to≡ to (fst x) eq1 | ==to≡ from (fst x) eq3 = ⊥-elim (p3 refl)
iValLemma4 {from} {to} {vF} {vT} {val} (x ∷ map) ac p1 p2 p3 | true | false | false
         rewrite (maybe≡ p2) | assocVal vT val (iVal (insert from (vF - val) map) ac)
         | commVal val (iVal (insert from (vF - val) map) ac)
         = cong (λ a → vT + a) (switchSides (iVal map ac) val
         (iVal (insert from (vF - val) map) ac) (iValLemma3 map ac p1))
iValLemma4 {from} {to} {vF} {vT} {val} (x ∷ map) ac p1 p2 p3 | false with from == (fst x) in eq2
iValLemma4 {from} {to} {vF} {vT} {val} (x ∷ map) ac p1 p2 p3 | false | true
         rewrite (maybe≡ p1) | assocVal vF (negValue val) (iVal (insert to (vT + val) map) ac)
         | commVal (negValue val) (iVal (insert to (vT + val) map) ac) 
         = cong (λ a → vF + a) (switchSides' (iVal map ac) val
         (iVal (insert to (vT + val) map) ac) (iValLemma3 map ac p2))
iValLemma4 {from} {to} {vF} {vT} {val} (x ∷ map) ac p1 p2 p3 | false | false
         = cong (λ a → (snd x) + a) (iValLemma4 map ac p1 p2 p3)

-- Fidelity Proof

initialFidelity : ∀ {s par}
  -> par ⊢ s
  -> fides s
initialFidelity {record { datum = .(_ , []) }}
                (TStart refl x₂ x₃ x₄) = x₄ 


fidelity : ∀ {s s' i par}
         -> fides s
         -> par ⊢ s ~[ i ]~> s'
         -> fides s'
         
fidelity {s@record { datum = tok , map }} {s'} refl
         (TOpen refl p2 p3 refl refl)
         rewrite iVal≡ s | iVal≡ s' = iValLemma1 map tok p3
       
fidelity {s@record { datum = tok , map }} {s'} refl
         (TClose refl p2 p3 refl refl)
         rewrite iVal≡ s | iVal≡ s' = iValLemma2 map tok p3
         
fidelity {s@record { datum = tok , map }} {s'} refl
         (TDeposit refl p2 p3 p4 refl refl) 
         rewrite iVal≡ s | iVal≡ s' = iValLemma3 map tok p3
         
fidelity {s@record { datum = tok , map }} {s'} refl
         (TWithdraw refl p2 p3 p4 p5 refl refl)
         rewrite iVal≡ s | iVal≡ s' = iValLemma3 map tok p3

fidelity {s@record { datum = tok , map }} {s'} refl
         (TTransfer refl p2 p3 p4 p5 p6 p7 refl refl)
         rewrite iVal≡ s | iVal≡ s' = iValLemma4 map tok p3 p4 p7


-- Combined state invariant predicate

invariant : State -> Set
invariant s = (valid s × fides s)

-- Invariant proofs
initialInvariant : ∀ {s par}
  -> par ⊢ s
  -> invariant s
initialInvariant p = (initialValidity p) , (initialFidelity p)

stateInvariant : ∀ {s s' i par}
  -> invariant s
  -> par ⊢ s ~[ i ]~> s'
  -> invariant s'
stateInvariant (valid , fides) p = validity valid p , fidelity fides p


-- Lemmas for Liquidity

makeIs : AccMap -> List Redeemer
makeIs [] = []
makeIs ((pkh , v) ∷ map) = (Withdraw pkh v) ∷ (Close pkh) ∷ (makeIs map)

lastSig : AccMap -> PubKeyHash -> PubKeyHash
lastSig [] pkh = pkh
lastSig (x ∷ []) pkh = x .fst
lastSig (x ∷ y ∷ map) pkh = lastSig (y ∷ map) pkh

sameLastSig' : ∀ {x sig sig'} (map : AccMap)
             -> lastSig (x ∷ map) sig ≡ lastSig (x ∷ map) sig'
sameLastSig' [] = refl
sameLastSig' (y ∷ map) = sameLastSig' map

sameLastSig : ∀ {pkh v sig} (map : AccMap)
              -> lastSig ((pkh , v) ∷ map) sig ≡ lastSig map pkh
sameLastSig [] = refl
sameLastSig (x ∷ []) = refl
sameLastSig (x ∷ y ∷ map) = sameLastSig' map

rwLookup : ∀ {b : Bool} {a : Set} { x y : Maybe a }
            -> b ≡ true
            -> (if b then x else y) ≡ x
rwLookup refl = refl

rwInsertDelete : ∀ {a : AssetClass} {b : Bool} { x y z : AccMap }
            -> b ≡ true
            -> x ≡ z
            -> (a , z) ≡ (a , (if b then x else y))
rwInsertDelete refl refl = refl

rwAccMap : ∀ (pkh : PubKeyHash) (val : Value) (map : AccMap)
           -> (pkh , val - val) ∷ map ≡ (pkh , emptyValue) ∷ map
rwAccMap pkh val map rewrite (v-v val) = refl

rwVal : ∀ (v1 v2 : Value)
            -> v1 ≡ (v2 + v1) - v2 
rwVal v1 v2 rewrite commVal v2 v1
            | assocVal v1 v2 (negValue v2)
            | v-v v2 = sym (addValIdR v1)

subValid : ∀ {x} (map : AccMap)
  -> All (\y -> geq (snd y) emptyValue ≡ true) (x ∷ map)
  -> All (λ y → geq (snd y) emptyValue ≡ true) map
subValid map (allCons {{i}} {{is}}) = is

subGeq : ∀ {x} (map : AccMap)
  -> All (\y -> geq (snd y) emptyValue ≡ true) (x ∷ map)
  -> geq (snd x) emptyValue ≡ true
subGeq map (allCons {{i}} {{is}}) = i

-- You can withdraw all money from each account and then close it, one by one

prop1 : ∀ {tok} {map : AccMap} (s s' : State) {par}
        -> datum s ≡ (tok , map)
        -> datum s' ≡ (tok , [])
        -> value s' ≡ minValue + assetClassValue tok 1
        -> tsig s' ≡ lastSig map (tsig s)
        -> value s ≡ iVal map tok --addValue (sumVal map) minValue --sumIVal map
        -> spends s ≡ spends s'
        -- -> mint s ≡ mint s'
        -> token s ≡ token s'
        -> valid s
        -> par ⊢ s ~[ (makeIs map) ]~* s'
        
prop1 record { datum = (tok , []) } record { datum = (tok' , map') }
  refl refl refl refl refl refl refl p = nil
prop1 s@record { datum = (tok , (pkh , v) ∷ map')
               ; spends = spends ; token = token }
      s'@record { datum = (tok , map'') } refl  refl refl
      refl refl refl refl p
      = cons {s' = st} (TWithdraw refl refl (rwLookup (n=n pkh))
        (subGeq map' p) (geq-refl v) (rwInsertDelete (n=n pkh)
        (rwAccMap pkh v map')) (rwVal (value st) v)) 
        (cons {s' = st'} (TClose refl refl (rwLookup (n=n pkh))
        (rwInsertDelete (n=n pkh) refl) refl )
        (prop1 st' s' refl refl refl (sameLastSig map')
        refl refl refl (subValid map' p)))
        
      where
      st = record
            { datum = tok ,
            ((pkh , emptyValue) ∷ map')
            ; value = iVal map' tok --addValue (sumVal map') minValue
            ; tsig = pkh
            ; spends = spends
            ; token = token }
            
      st' = record
             { datum = tok , map'
             ; value = iVal map' tok --addValue (sumVal map') minValue --sumIVal map'
             ; tsig = pkh
             ; spends = spends
             ; token = token }

--Liquidity (For any state that is valid and has valid parameters,
--there exists another state and some inputs such that we can transition
--there and have no value left in the contract)

{-
liqudity' : ∀ (s : State) (par : MParams) 
  -> Invariant s
  -> ∃[ s' ] ∃[ is ] ((par ⊢ s ~[ is ]~* s') × ( ∃[ i ] par ⊢ s' ~[ i ]~> ))
liqudity' = {!!}
-}

liquidity : ∀ (s : State) (par : MParams)
          -> invariant s
          -> ∃[ is ] par ⊢ s ~[ is ]~>*


liquidity s@record { datum = (tok , map) ; spends = spends
  ; token = token } par (p1 , p2) rewrite iVal≡ s
  = ⟨ (makeIs map ++ [ Stop ]) ,
    (fin (prop1 s s' refl refl refl refl p2 refl refl p1)
    (TStop refl) ) ⟩ 
  where
  s' = record
       { datum = tok , []
       ; value = minValue + assetClassValue tok 1
       ; tsig = lastSig map (tsig s)
       ; spends = spends
       ; token = token }
       
minValLiquidity : ∀ (s : State) (par : MParams)
          -> invariant s
          -> ∃[ s' ] ∃[ is ]
             ((par ⊢ s ~[ is ]~* s')
             × (value s' ≡ (minValue + assetClassValue (s' .datum .fst) 1)))

minValLiquidity s@record { datum = (tok , map) ; spends = spends
  ; token = token } par (p1 , p2) rewrite iVal≡ s
  = ⟨ s' , ⟨ (makeIs map) ,
    ((prop1 s s' refl refl refl refl p2 refl refl p1) , refl) ⟩ ⟩
    
  where
  s' = record
       { datum = tok , []
       ; value = minValue + assetClassValue tok 1
       ; tsig = lastSig map (tsig s)
       ; spends = spends
       ; token = token }
       
       
-- Multi-Step transition lemma
lemmaMultiStep : ∀ (s s' s'' : State) (is is' : List Redeemer) {par}
                   -> par ⊢  s  ~[ is  ]~* s'
                   -> par ⊢ s' ~[ is' ]~* s''
                   -> par ⊢ s  ~[ is ++ is' ]~* s''
lemmaMultiStep s .s s'' [] is' nil p2 = p2
lemmaMultiStep s s' s'' (x ∷ is) is' (cons {s' = s'''} p1 p2) p3 = cons p1 (lemmaMultiStep s''' s' s'' is is' p2 p3)


originStateRewrite : ∀ {sig spn tok} (par : MParams) (s s' : State) (i : Redeemer)
                 -> par ⊢ s ~[ i ]~> s'
                 -> par ⊢ record
                           { datum = datum s
                           ; value = value s
                           ; tsig = sig
                           ; spends = spn
                           ; token = tok
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

targetStateRewrite : ∀ {spn tok} (par : MParams) (s s' : State) (i : Redeemer)
                 -> par ⊢ s ~[ i ]~> s'
                 -> par ⊢ s ~[ i ]~> record
                                      { datum = datum s'
                                      ; value = value s'
                                      ; tsig = tsig s'
                                      ; spends = spn
                                      ; token = tok
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
        ; token = 0 , 0
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





-- Extracting the State from ScriptContext

sig : ScriptContext -> PubKeyHash
sig = ScriptContext.signature

iRef : ScriptContext -> TxOutRef
iRef = ScriptContext.inputRef

-- Initialing State for normal transitions
getS : Datum -> ScriptContext -> State
getS (tok , map) ctx = record
                               { datum = (tok , map)
                               ; value = oldValue ctx
                               ; tsig = 0 
                               ; spends = 0
                               ; token = 0 , 0
                               }



-- Initial State when we mint the token and put the smart contract on the blockchain
getMintS : TokenName -> ScriptContext -> State
getMintS tn ctx = record
                { datum = newDatum ctx
                ; value = newValue ctx
                ; tsig = ScriptContext.signature ctx
                ; spends = ScriptContext.inputRef ctx
              --  ; mint = getMintedAmount ctx
                ; token = ownAssetClass tn ctx
                }

-- Resulting State for normal transitions
getS' : ScriptContext -> State
getS' ctx = record
                               { datum = newDatum ctx
                               ; value = newValue ctx
                               ; tsig = sig ctx
                               ; spends = iRef ctx
                          --     ; mint = getMintedAmount ctx
                               ; token = (0 , 0)
                               }



-- Getting the Model parameters from the parameters of the validator and minting policy
getPar : TxOutRef -> TokenName -> MParams
getPar oref tn = record
                     { --validatorAddress = adr
                      uniqueId = oref
                     ; threadTokName = tn
                     }

-- Defining the components for the equivalence relation between the model and the validator.

data Phase : Set where
  Initial  : Phase
  Running  : Phase
  Final    : Phase

record Argument : Set where
  field
    adr  : Address
    oref : TxOutRef
    tn   : TokenName
    dat  : Datum
    red  : Redeemer
    ctx  : ScriptContext 
open Argument

-- The Equivalence Relation
record _≈_ {A : Set} (f : A -> Bool) (R : A -> Set) : Set where
  field to   : ∀ {a} -> f a ≡ true -> R a
        from : ∀ {a} -> R a        -> f a ≡ true

-- If we mint exactly 1 token we are in the Initial Phase
-- If we burn a token and the input is Close, we are in the Final Phase
-- Otherwise we are in the Running Phase
Classifier : Argument -> Phase
Classifier record { adr = adr ; oref = oref ; dat = dat ; red = red ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (+_ zero) } } = Running
Classifier record { adr = adr ; oref = oref ; dat = dat ; red = red ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = +[1+ zero ] } } = Initial
Classifier record { adr = adr ; oref = oref ; dat = dat ; red = red ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = +[1+ N.suc n ] } } = Running
Classifier record { adr = adr ; oref = oref ; dat = dat ; red = red ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc (N.suc n)) } } = Running
Classifier record { adr = adr ; oref = oref ; dat = dat ; red = (Open x) ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero)  } } = Running
Classifier record { adr = adr ; oref = oref ; dat = dat ; red = (Close x) ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } = Running
Classifier record { adr = adr ; oref = oref ; dat = dat ; red = (Withdraw x x₁) ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } = Running
Classifier record { adr = adr ; oref = oref ; dat = dat ; red = (Deposit x x₁) ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } = Running
Classifier record { adr = adr ; oref = oref ; dat = dat ; red = (Transfer x x₁ x₂) ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } = Running
Classifier record { adr = adr ; oref = oref ; dat = dat ; red = Stop ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } = Final

-- The Validator as a function returning a boolean
totalF : Argument -> Bool
totalF arg with Classifier arg
... | Initial = agdaPolicy (arg .adr) (arg .oref) (arg .tn) tt (arg .ctx)
... | Running = agdaValidator (arg .dat) (arg .red) (arg .ctx) 
... | Final = agdaValidator (arg .dat) (arg .red) (arg .ctx) &&
              agdaPolicy (arg .adr) (arg .oref) (arg .tn) tt (arg .ctx)




-- The State Transition System as a relation
totalR : Argument -> Set
totalR arg with Classifier arg
... | Initial = getPar (arg .oref) (arg .tn) ⊢ getMintS (arg .tn) (arg .ctx)
                × continuing (arg .ctx) ≡ true
                × getMintedAmount (arg .ctx) ≡ 1
                × checkTokenOutAddr (arg .adr) (ownAssetClass (arg .tn) (arg .ctx)) (arg .ctx) ≡ true

... | Running = getPar (arg .oref) (arg .tn)
                ⊢ getS (arg .dat) (arg .ctx) ~[ (arg .red) ]~> getS' (arg .ctx)
                × continuing (arg .ctx) ≡ true
                × checkTokenIn (arg .dat .fst) (arg .ctx) ≡ true
                × checkTokenOut (arg .dat .fst) (arg .ctx) ≡ true
                
... | Final = getPar(arg .oref) (arg .tn)
                 ⊢ getS (arg .dat) (arg .ctx)  ~[ (arg .red) ]~>
                 × continuing (arg .ctx) ≡ false
                 × getMintedAmount (arg .ctx) ≡ -1
                 × checkTokenIn (arg .dat .fst) (arg .ctx) ≡ true




-- Lemmas and helper functions for validator returning true implies transition

==pto≡ : ∀ (a b : PubKeyHash × Value) -> (a == b) ≡ true -> a ≡ b
==pto≡ (fst1 , snd1) (fst2 , snd2) pf
  rewrite (==to≡ fst1 fst2 (get pf))
        | (==vto≡ snd1 snd2 (go (fst1 == fst2) pf)) = refl
        
==Lto≡ : ∀ (a b : AccMap) -> (a == b) ≡ true -> a ≡ b
==Lto≡ [] [] pf = refl
==Lto≡ (x ∷ a) (y ∷ b) pf
  rewrite (==pto≡ x y (get pf)) = cong (λ x → y ∷ x) ((==Lto≡ a b (go (x == y) pf)))

map=map : ∀ (l : AccMap) -> (l == l) ≡ true
map=map [] = refl
map=map (x ∷ l) rewrite n=n (fst x) | v=v (snd x) = map=map l

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

--?

-- Performing a transition implies that the validator returns true
transitionImpliesValidator : ∀ {par} (d : Datum) (i : Redeemer) (ctx : ScriptContext)
                           -> (par ⊢ getS d ctx ~[ i ]~> getS' ctx
                               × continuing ctx ≡ true
                               × checkTokenIn (d .fst) ctx ≡ true
                               × checkTokenOut (d .fst) ctx ≡ true)
                           -> agdaValidator d i ctx ≡ true
transitionImpliesValidator (tok , map) (Open pkh) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = mint ; tokCurrSymbol = cs } ((TOpen refl refl p3 refl refl) , refl , refl , refl) rewrite p3 | n=n pkh | map=map (insert pkh emptyValue map) | v=v inputVal | t=t tok = refl
transitionImpliesValidator (tok , map) (Close pkh) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = mint ; tokCurrSymbol = cs } ((TClose refl refl p3 refl refl) , refl , refl , refl) rewrite p3 | n=n pkh | map=map (delete pkh map) | v=v inputVal | t=t tok = refl
transitionImpliesValidator (tok , map) (Withdraw pkh val) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = mint ; tokCurrSymbol = cs } ((TWithdraw {v = v} refl refl p3 p4 p5 refl refl) , refl , refl , refl) rewrite p3 | n=n pkh | v=v (inputVal - val) | map=map (insert pkh (v - val) map) | p4 | p5 | t=t tok = refl
transitionImpliesValidator (tok , map) (Deposit pkh val) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = mint ; tokCurrSymbol = cs } ((TDeposit {v = v} refl refl p3 p4 refl refl) , refl , refl , refl) rewrite p3 | n=n pkh | v=v (inputVal + val) | map=map (insert pkh (v + val) map) | p4 | t=t tok = refl
transitionImpliesValidator (tok , map) (Transfer from to val) record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok' , map') ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = mint ; tokCurrSymbol = cs } ((TTransfer {vF = vF} {vT = vT} refl refl p3 p4 p5 p6 p7 refl refl) , refl , refl , refl) rewrite p3 | p4 | ≢to/= from to p7 | n=n from | v=v inputVal | map=map (insert from (vF - val) (insert to (vT + val) map)) | p5 | p6 | t=t tok = refl



-- Being in the initial model state implies we can mint a token
initialImpliesMinting : ∀ (adr : Address) (oref : TxOutRef) (tn : TokenName) (top : ⊤) (ctx : ScriptContext)
                           -> (getPar oref tn ⊢ getMintS tn ctx
                               × continuing ctx ≡ true
                               × getMintedAmount ctx ≡ 1
                               × checkTokenOut (newDatum ctx .fst) ctx ≡ true)
                           -> agdaPolicy adr oref tn top ctx ≡ true
initialImpliesMinting adr oref tn top record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , l) ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; tokCurrSymbol = cs } ((TStart refl refl refl p) , refl , refl , refl)
  rewrite sym p | v=v outputVal | n=n oref | t=t tok = refl 

-- Getting to the terminal state implies that the validator returns true and a token can be burned
stopImpliesBoth : ∀ {tn par i} (d : Datum) (adr : Address) (oref : TxOutRef) (ctx : ScriptContext)   
  -> (par ⊢ getS d ctx ~[ i ]~>
      × continuing ctx ≡ false
      × getMintedAmount ctx ≡ -1
      × checkTokenIn (d .fst) ctx ≡ true)
  -> (agdaValidator d i ctx && agdaPolicy adr oref tn tt ctx) ≡ true
stopImpliesBoth d adr oref ctx ((TStop refl) , refl , refl , refl) = refl



--Validator returning true implies we can perform a transition
validatorImpliesTransition : ∀ {par} (d : Datum) (i : Redeemer) (ctx : ScriptContext) 
                           -> i ≢ Stop
                           -> (pf : agdaValidator d i ctx ≡ true)
                           -> (par ⊢ getS d ctx ~[ i ]~> getS' ctx
                              × continuing ctx ≡ true
                              × checkTokenIn (d .fst) ctx ≡ true
                              × checkTokenOut (d .fst) ctx ≡ true)
                              

validatorImpliesTransition (tok , map) (Open pkh) ctx iv pf with lookup pkh map in eq
validatorImpliesTransition (tok , map) (Open pkh) ctx iv pf | Just _ = ⊥-elim (&&4false (checkTokenIn tok ctx) (checkTokenOut tok ctx) (continuing ctx) (sig ctx == pkh) pf)
validatorImpliesTransition (tok , map) (Open pkh) ctx iv pf | Nothing with newDatum ctx in eq2
validatorImpliesTransition (tok , map) (Open pkh) ctx iv pf | Nothing | tok' , map'
     rewrite sym (==tto≡ tok' tok (get (get (go (sig ctx == pkh) ((go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))))
             | ==Lto≡ map' (insert pkh emptyValue map) (go (tok' == tok) (get (go (sig ctx == pkh) 
             (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))) 
             = (TOpen refl ((==to≡ (sig ctx) pkh (get (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))) )
               eq eq2 (==vto≡ (newValue ctx) (oldValue ctx) (go ((tok' , map') == (tok , insert pkh emptyValue map)) (go (sig ctx == pkh) (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))) , (get (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))) , (get pf) , (get (go (checkTokenIn tok ctx) pf)))  


validatorImpliesTransition (tok , map) (Close pkh) ctx iv pf with lookup pkh map in eq
validatorImpliesTransition (tok , map) (Close pkh) ctx iv pf | Nothing = ⊥-elim (&&4false (checkTokenIn tok ctx) (checkTokenOut tok ctx) (continuing ctx) (sig ctx == pkh) pf) 
validatorImpliesTransition (tok , map) (Close pkh) ctx iv pf | Just v with newDatum ctx in eq2
validatorImpliesTransition (tok , map) (Close pkh) ctx iv pf | Just v | tok' , map' rewrite
            ==vto≡ v emptyValue (get (go (sig ctx == pkh)
            (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))
            | ==tto≡ tok' tok (get (get (go (v == emptyValue) (go (sig ctx == pkh) (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))))
            | ==Lto≡ map' (delete pkh map) (go (tok' == tok) (get (go (v == emptyValue) (go (sig ctx == pkh) 
            (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))) 
            = (TClose refl (==to≡ (sig ctx) pkh (get (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))
              eq eq2 (==vto≡ (newValue ctx) (oldValue ctx) (go ( (tok' , map') == (tok , delete pkh map)) (go (v == emptyValue)
              (go (sig ctx == pkh) (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))) , (get (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))) , (get pf) , (get (go (checkTokenIn tok ctx) pf))) 
              

validatorImpliesTransition (tok , map) (Withdraw pkh val) ctx iv pf with lookup pkh map in eq
validatorImpliesTransition (tok , map) (Withdraw pkh val) ctx iv pf | Nothing = ⊥-elim (&&4false (checkTokenIn tok ctx) (checkTokenOut tok ctx) (continuing ctx) (sig ctx == pkh) pf)
validatorImpliesTransition (tok , map) (Withdraw pkh val) ctx iv pf | Just v with newDatum ctx in eq2
validatorImpliesTransition (tok , map) (Withdraw pkh val) ctx iv pf | Just v | tok' , map'
  rewrite sym (==tto≡ tok' tok (get (go (geq v val) (go (geq val emptyValue) (get (go (sig ctx == pkh)
             (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))))))
             | (==Lto≡ map' (insert pkh (v - val) map)
             (go (tok' == tok) (go (geq v val) (go (geq val emptyValue) (get (go (sig ctx == pkh)
             (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))))))
            = (TWithdraw refl (==to≡ (sig ctx) pkh (get (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))
            eq (get (get (go (sig ctx == pkh) (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))
            (get (go (geq val emptyValue) (get (go (sig ctx == pkh) (go (continuing ctx)
            (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))) eq2 
            ((==vto≡ (newValue ctx) ((oldValue ctx) - val) (go (checkWithdraw' tok (Just v) pkh val map (tok' , map'))
             ((go (sig ctx == pkh) (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))) ) , (get (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))) , (get pf) , (get (go (checkTokenIn tok ctx) pf))) 

validatorImpliesTransition (tok , map) (Deposit pkh val) ctx iv pf with lookup pkh map in eq
validatorImpliesTransition (tok , map) (Deposit pkh val) ctx iv pf | Nothing = ⊥-elim (&&4false (checkTokenIn tok ctx) (checkTokenOut tok ctx) (continuing ctx) (sig ctx == pkh) pf)
validatorImpliesTransition (tok , map) (Deposit pkh val) ctx iv pf | Just v with newDatum ctx in eq2
validatorImpliesTransition (tok , map) (Deposit pkh val) ctx iv pf | Just v | tok' , map'
  rewrite sym (==tto≡ tok' tok (get (go (geq val emptyValue) (get (go (sig ctx == pkh) (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))))
             | ==Lto≡ map' (insert pkh (v + val) map)
             (go (tok' == tok) (go (geq val emptyValue)  (get (go (sig ctx == pkh)
             (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))))
             = (TDeposit refl (==to≡ (sig ctx) pkh (get (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))
             eq (get (get (go (sig ctx == pkh) (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))
             eq2 (==vto≡ (newValue ctx) ((oldValue ctx) + val) (go (checkDeposit' tok (Just v) pkh val map (tok' , map'))
             ((go (sig ctx == pkh) (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))) , (get (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))) , (get pf) , (get (go (checkTokenIn tok ctx) pf))) 

validatorImpliesTransition (tok , map) (Transfer from to val) ctx iv pf with lookup from map in eq1
validatorImpliesTransition (tok , map) (Transfer from to val) ctx iv pf | Nothing
  = ⊥-elim (&&4false (checkTokenIn tok ctx) (checkTokenOut tok ctx) (continuing ctx) (sig ctx == from) pf)
validatorImpliesTransition (tok , map) (Transfer from to val) ctx iv pf | Just vF with lookup to map in eq2
validatorImpliesTransition (tok , map) (Transfer from to val) ctx iv pf | Just vF | Nothing
  = ⊥-elim (&&4false (checkTokenIn tok ctx) (checkTokenOut tok ctx) (continuing ctx) (sig ctx == from) pf)
validatorImpliesTransition (tok , map) (Transfer from to val) ctx iv pf | Just vF | Just vT with newDatum ctx in eq3
validatorImpliesTransition (tok , map) (Transfer from to val) ctx iv pf | Just vF | Just vT | tok' , map'
  rewrite sym (==tto≡ tok' tok (get (go (from /= to) (go (geq vF val) (go (geq val emptyValue) (get (go (sig ctx == from)
  (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))))))
  | ==Lto≡ map' (insert from (vF - val) (insert to (vT + val) map))
  (go (tok' == tok) (go (from /= to) (go (geq vF val) (go (geq val emptyValue) (get (go (sig ctx == from)
  (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))))))
    = (TTransfer refl (==to≡ (sig ctx) from (get (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))) eq1 eq2
    (get (get (go (sig ctx == from) (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))
    (get (go (geq val emptyValue) (get (go (sig ctx == from) 
    (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))))
    (/=to≢ from to (get (go (geq vF val) (go (geq val emptyValue) (get (go (sig ctx == from)
    (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))))))))) eq3  
    (==vto≡ (newValue ctx) (oldValue ctx) (go (checkTransfer' tok (Just vF) (Just vT) from to val map (tok' , map')) (go (sig ctx == from) (go (continuing ctx) (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf)))))) , (get (go (checkTokenOut tok ctx) (go (checkTokenIn tok ctx) pf))) , (get pf) , (get (go (checkTokenIn tok ctx) pf))) 
validatorImpliesTransition (tok , map) Stop ctx iv pf = ⊥-elim (iv refl)


-- Minting the token implies we are in the initial state of our model
mintingImpliesInitial : ∀ (adr : Address) (oref : TxOutRef) (tn : TokenName) (top : ⊤) (ctx : ScriptContext)
                           -> getMintedAmount ctx ≡ 1
                           -> (pf : agdaPolicy adr oref tn top ctx ≡ true)
                           -> (getPar oref tn ⊢ getMintS tn ctx
                              × continuing ctx ≡ true
                              × getMintedAmount ctx ≡ 1
                              × checkTokenOut (newDatum ctx .fst) ctx ≡ true)
mintingImpliesInitial adr oref tn top ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , l) ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut =  hasTokenOut ; mint = + 1 ; tokCurrSymbol = cs } refl pf
  rewrite ==Lto≡ l [] (go ((cs , tn) == tok) (get (go (inputRef == oref) (go continues pf))))
  | sym (==tto≡ (cs , tn) tok (get (get (go (inputRef == oref) (go continues pf)))))
  = (TStart refl (==to≡ inputRef oref (get (go continues pf))) refl
    (==vto≡ outputVal (minValue + assetClassValue (cs , tn) 1) (go hasTokenOut (go (checkDatum adr tn ctx) (go (inputRef == oref) (go continues pf))))) 
    , get pf , refl , (get (go (checkDatum adr tn ctx) (go (inputRef == oref) (go continues pf)))) )


-- Validator returning true and burning a token implies we are in the terminal state 
bothImplyStop : ∀ {tn par} (d : Datum) (adr : Address) (oref : TxOutRef) (i : Redeemer) (ctx : ScriptContext) 
                   -> getMintedAmount ctx ≡ -1
                   -> (agdaValidator d i ctx && agdaPolicy adr oref tn tt ctx) ≡ true
                   -> (par ⊢ getS d ctx ~[ i ]~>
                      × continuing ctx ≡ false
                      × getMintedAmount ctx ≡ -1
                      × checkTokenIn (d .fst) ctx ≡ true )
bothImplyStop d adr oref (Open pkh) record { tokenIn = tokenIn ; tokenOut = tokenOut ; continues = false } refl p2 = ⊥-elim (get⊥ (sym (go tokenOut (go tokenIn (get p2)))))
bothImplyStop d adr oref i@(Open pkh) ctx@record { continues = true } refl p2 = ⊥-elim (get⊥ (sym (go (agdaValidator d i ctx) p2) ))
bothImplyStop d adr oref (Close pkh) record { tokenIn = tokenIn ; tokenOut = tokenOut ; continues = false } refl p2 = ⊥-elim (get⊥ (sym (go tokenOut (go tokenIn (get p2)))))
bothImplyStop d adr oref i@(Close pkh) ctx@record { continues = true } refl p2 = ⊥-elim (get⊥ (sym (go (agdaValidator d i ctx) p2) ))
bothImplyStop d adr oref (Withdraw pkh v) record { tokenIn = tokenIn ; tokenOut = tokenOut ; continues = false } refl p2 = ⊥-elim (get⊥ (sym (go tokenOut (go tokenIn (get p2)))))
bothImplyStop d adr oref i@(Withdraw pkh v) ctx@record { continues = true } refl p2 = ⊥-elim (get⊥ (sym (go (agdaValidator d i ctx) p2) ))
bothImplyStop d adr oref (Deposit pkh v) record { tokenIn = tokenIn ; tokenOut = tokenOut ; continues = false } refl p2 = ⊥-elim (get⊥ (sym (go tokenOut (go tokenIn (get p2)))))
bothImplyStop d adr oref i@(Deposit pkh v) ctx@record { continues = true } refl p2 = ⊥-elim (get⊥ (sym (go (agdaValidator d i ctx) p2) ))
bothImplyStop d adr oref (Transfer from to v) record { tokenIn = tokenIn ; tokenOut = tokenOut ; continues = false } refl p2 = ⊥-elim (get⊥ (sym (go tokenOut (go tokenIn (get p2)))))
bothImplyStop d adr oref i@(Transfer from to v) ctx@record { continues = true } refl p2 = ⊥-elim (get⊥ (sym (go (agdaValidator d i ctx) p2) ))
bothImplyStop d adr oref Stop ctx refl p2 = (TStop (==Lto≡ (snd d) [] (go (not (continuing ctx)) (go (checkTokenIn (d .fst) ctx) (get p2)))) , (unNot (get (go (checkTokenIn (d .fst) ctx) (get p2)))) , refl , (get (get p2)))

-- Lemma for when the input is Stop
removeStop : ∀ {par : MParams} (arg : Argument) -> (getMintedAmount (ctx arg) ≢ (negsuc zero))
               -> (agdaValidator (arg .dat) (arg .red) (arg .ctx) ≡ true)
               -> par ⊢ getS (arg .dat) (arg .ctx)  ~[ (arg .red) ]~> getS' (arg .ctx)
                  × continuing (arg .ctx) ≡ true
                  × checkTokenIn (arg .dat .fst) (arg .ctx) ≡ true
                  × checkTokenOut (arg .dat .fst) (arg .ctx) ≡ true
removeStop record { dat = dat ; red = (Open pkh) ; ctx = ctx } p1 p2 = validatorImpliesTransition dat (Open pkh) ctx (λ ()) p2
removeStop record { dat = dat ; red = (Close pkh) ; ctx = ctx } p1 p2 = validatorImpliesTransition dat (Close pkh) ctx (λ ()) p2
removeStop record { dat = dat ; red = (Withdraw pkh v) ; ctx = ctx } p1 p2 = validatorImpliesTransition dat (Withdraw pkh v) ctx (λ ()) p2
removeStop record { dat = dat ; red = (Deposit pkh v) ; ctx = ctx } p1 p2 = validatorImpliesTransition dat (Deposit pkh v) ctx (λ ()) p2
removeStop record { dat = dat ; red = (Transfer from to v) ; ctx = ctx } p1 p2 = validatorImpliesTransition dat (Transfer from to v) ctx (λ ()) p2
removeStop record { dat = dat ; red = Stop ; ctx = ctx } p1 p2 = ⊥-elim (p1 (==ito≡ (getMintedAmount ctx) (negsuc 0) (get (go (checkTokenIn (dat .fst) ctx) p2))))

-- The proof of equivalence
totalEquiv : totalF ≈ totalR
totalEquiv = record { to = λ { { arg@record { adr = adr ; oref = oref ; dat = dat ; red = red ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (+_ zero) } } } x → removeStop arg (λ ()) x ;
                                { record { adr = adr ; oref = oref ; tn = tn ; dat = dat ; red = red ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = +[1+ zero ] } } } x → mintingImpliesInitial adr oref tn tt ctx refl x ;
                                { arg@record { adr = adr ; oref = oref ; dat = dat ; red = red ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = +[1+ N.suc n ] } } } x → removeStop arg (λ ()) x ;
                                { arg@record { adr = adr ; oref = oref ; dat = dat ; red = red ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc (N.suc n)) } } } x → removeStop arg (λ ()) x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; red = (Open pkh) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } } x → validatorImpliesTransition dat (Open pkh) ctx (λ ()) x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; red = (Close pkh) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } } x → validatorImpliesTransition dat (Close pkh) ctx (λ ()) x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; red = (Deposit pkh v) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } } x → validatorImpliesTransition dat (Deposit pkh v) ctx (λ ()) x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; red = (Withdraw pkh v) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } } x → validatorImpliesTransition dat (Withdraw pkh v) ctx (λ ()) x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; red = (Transfer from to v) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } } x → validatorImpliesTransition dat (Transfer from to v) ctx (λ ()) x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; red = Stop ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } } x → bothImplyStop {0} dat adr oref Stop ctx refl x }
                     ; from = λ { { arg@record { adr = adr ; oref = oref ; dat = dat ; red = red ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (+_ zero) } } } x → transitionImpliesValidator dat red ctx x ;
                                { record { adr = adr ; oref = oref ; tn = tn ; dat = dat ; red = red ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = +[1+ zero ] } } } x → initialImpliesMinting adr oref tn tt ctx x ;
                                { arg@record { adr = adr ; oref = oref ; dat = dat ; red = red ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = +[1+ N.suc n ] } } } x → transitionImpliesValidator dat red ctx x ;
                                { arg@record { adr = adr ; oref = oref ; dat = dat ; red = red ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc (N.suc n)) } } } x → transitionImpliesValidator dat red ctx x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; red = (Open pkh) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } } x → transitionImpliesValidator dat (Open pkh) ctx x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; red = (Close pkh) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } } x → transitionImpliesValidator dat (Close pkh) ctx x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; red = (Deposit pkh v) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } } x → transitionImpliesValidator dat (Deposit pkh v) ctx x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; red = (Withdraw pkh v) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } } x → transitionImpliesValidator dat (Withdraw pkh v) ctx x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; red = (Transfer from to v) ; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } } x → transitionImpliesValidator dat (Transfer from to v) ctx x ;
                                { record { adr = adr ; oref = oref ; dat = dat ; red = Stop; ctx = ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; tokenIn = hasTokenIn ; tokenOut = hasTokenOut ; mint = (negsuc zero) } } } x → stopImpliesBoth {0} dat adr oref ctx x } } 



