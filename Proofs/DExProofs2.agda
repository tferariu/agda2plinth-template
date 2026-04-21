open import Validators.DEx2
open import Lib
open import Value

open import Agda.Builtin.Char
open import Agda.Builtin.Equality
open import Agda.Builtin.Bool
import Data.Nat as N
open import Data.Integer.Base hiding (_+_; _-_)
open import Data.Integer.Properties
open import Agda.Builtin.Int
open import Agda.Builtin.Nat renaming (_==_ to eqNat; _<_ to ltNat; _+_ to addNat; _-_ to monusNat; _*_ to mulNat)
open import Data.List hiding (lookup)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality.Core
open import Data.Empty
open import Data.Sum.Base
import Data.Sign.Base as Sign
open import Data.Product using ( ∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩; _×_ to _xx_)
open import Haskell.Prim hiding (⊥) -- ; All)
open import Haskell.Prim.Integer
open import Haskell.Prim.Bool
open import Haskell.Prim.Eq
open import Haskell.Prim.Ord
open import Haskell.Prim.Maybe
open import Haskell.Prim.Tuple
open import Haskell.Prim.Ord using (_<=_ ; _>=_)
open import Haskell.Prim using (lengthNat)
open import Haskell.Prelude using (lookup ; _+_ ; _-_)

open import ProofLib

module Proofs.DExProofs2 where

-- Model and proofs for the Limit Order Book Distributed Exchange contract

-- The States of the State Transition System
record State : Set where
  field
    datum      : Datum
    value      : Value  
    payVal     : Value
    tsig       : PubKeyHash
    spends     : TxOutRef
    token      : AssetClass
open State

-- Model paramets consisting of the combined parameters of the validator and minting policy
record MParams : Set where
    field
     --   validatorAddress : Address
        uniqueId         : TxOutRef
        threadTokName    : TokenName
        sellCurr         : AssetClass
        buyCurr          : AssetClass
open MParams public

-- Transition Rules of the State Transition Model

-- Initial State Transition
data _⊢_ : MParams -> State -> Set where

  TStart : ∀ {par s l}
    -> datum s ≡ ((token s) , l)
    -> uniqueId par ≡ spends s 
    -> token s .snd ≡ threadTokName par
    -> checkRational (ratio l) ≡ true
    -------------------
    -> par ⊢ s

-- Running State Transitions
data _⊢_~[_]~>_ : MParams -> State -> Redeemer -> State -> Set where
 
  TUpdate : ∀ {v r s s' par}
    -> owner (snd (datum s)) ≡ tsig s'
    -> value s' ≡ v 
    -> datum s' ≡ ((fst (datum s)) , (record { ratio = r ; owner = owner (snd (datum s)) })) 
    -> checkRational r ≡ true 
    -> checkMinValue v ≡ true
    -------------------
    -> par ⊢ s ~[ (Update v r) ]~> s'

  TExchange : ∀ {amt pkh s s' par}
    -> value s' + assetClassValue (sellCurr par) amt ≡ value s 
    -> datum s' ≡ datum s
    -> ratioCompare amt (assetClassValueOf (payVal s') (buyCurr par)) (ratio (snd (datum s))) ≡ true
    -> checkMinValue (payVal s') ≡ true
    -------------------
    -> par ⊢ s ~[ (Exchange amt pkh) ]~> s'

-- Terminal State Transition
data _⊢_~[_]~|_ : MParams -> State -> Redeemer -> State -> Set where

  TStop : ∀ {s s' par}
    -> owner (snd (datum s)) ≡ tsig s'
    -------------------
    -> par ⊢ s ~[ Stop ]~| s'
    

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


{-fin : ∀ { par s s' is }
    -> par ⊢ s ~[ Stop ]~| s'
    -------------------------
    -> par ⊢ s ~[ ((Stop) ∷ is) ]~* s'-}

data _⊢_~[_]~*|_ : MParams -> State -> List Redeemer -> State -> Set where

  fin : ∀ { par s s' s'' is i }
    -> par ⊢ s ~[ is ]~* s'
    -> par ⊢ s' ~[ i ]~| s''
    -------------------------
    -> par ⊢ s ~[ (is ++ [ i ]) ]~*| s''

-- State Validity Predicate
valid : State -> Set 
valid s = checkRational (ratio (snd (datum s))) ≡ true 

--State Validity Invariant
validStateInitial : ∀ {s par}
  -> par ⊢ s
  -> valid s
validStateInitial {record { datum = .(token₁ , _) ; value = value₁ ; payVal = payVal₁ ; tsig = tsig₁ ; spends = spends₁ ; token = token₁ }} (TStart refl p2 p3 p4) = p4

validStateTransition : ∀ {s s' : State} {i par}
  -> valid s
  -> par ⊢ s ~[ i ]~> s'
  -> valid s'
validStateTransition v (TUpdate x x₁ refl x₃ x₄ ) = x₃
validStateTransition v (TExchange x refl x₂ x₃) = v


--Liquidity (For any state that is valid and has valid parameters,
--there exists another state and some inputs such that we can transition
--there and have no value left in the contract)
liquidity : ∀ (par : MParams) (s : State) 
          -> valid s
          -> ∃[ s' ] ∃[ is ] ((par ⊢ s ~[ is ]~*| s') × (value s' ≡ emptyValue) )

liquidity par s v = ⟨ s' , ⟨  Stop ∷ [] , (fin nil (TStop refl) , refl) ⟩ ⟩
  where
    s' = record
          { datum = datum s
          ; value = emptyValue
          ; payVal = emptyValue
          ; tsig = owner (snd (datum s))
          ; spends = zero
          ; token = fst (datum s)
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
              ; payVal = 0
              ; tsig = 0 
           --   ; continues = true 
              ; spends = 0 
           --   ; hasToken = checkTokenIn tok ctx
           --   ; mint = 0 
              ; token = (0 , 0)
              }

-- Initial State when we mint the token and put the smart contract on the blockchain
getMintS : TokenName -> ScriptContext -> State
getMintS tn ctx = record
             { datum = newDatum ctx
             ; value = newValue ctx
             ; payVal = 0
             ; tsig = sig ctx
         --    ; continues = continuing ctx
             ; spends = iRef ctx
         --    ; hasToken = checkTokenOut (ownAssetClass tn ctx) ctx
         --    ; mint = getMintedAmount ctx
             ; token = ownAssetClass tn ctx
             }

-- Resulting State for normal transitions
getS' : Datum -> ScriptContext -> State
getS' (tok , lab) ctx = record
             { datum = newDatum ctx
             ; value = newValue ctx
             ; payVal = getPayment (owner lab) ctx
             ; tsig = sig ctx
       --      ; continues = continuing ctx
             ; spends = iRef ctx
      --       ; hasToken = checkTokenOut tok ctx
      --       ; mint = getMintedAmount ctx
             ; token = tok
             }

-- Getting the Model parameters from the parameters of the validator and minting policy
getPar : Params -> TxOutRef -> TokenName -> MParams
getPar record { sellCurr = sellC ; buyCurr = buyC } oref tn
  = record
      { -- validatorAddress = adr --: Address
       uniqueId         = oref --: TxOutRef
      ; threadTokName    = tn --: TokenName
      ; sellCurr         = sellC --: AssetClass
      ; buyCurr          = buyC }--address = adr
                                                      --    ; outputRef = oref
                                                      --    ; tokName = tn
                                                      --    ; sellC = sellC
                                                      --    ; buyC = buyC
                                                      --    } 


-- Lemma for validator returning true implies transition
==Lto≡ : ∀ (l l' : Label)
       -> (l == l') ≡ true
       -> l ≡ l' 
==Lto≡ record { ratio = ratio ; owner = owner } record { ratio = ratio' ; owner = owner' } pf
  rewrite ==rto≡ {ratio} {ratio'} (get pf) | ==to≡ owner owner' (go (ratio == ratio') pf) = refl
  
==dto≡ : {a b : Datum} -> (a == b) ≡ true -> a ≡ b
==dto≡ {tok , l} {tok' , l'} p rewrite ==tto≡ tok tok' (get p) | ==Lto≡ l l' (go (tok == tok') p) = refl



--Validator returning true implies that we can perform a transition
validatorImpliesTransition : ∀ {oref tn} (par : Params) (d : Datum) (i : Redeemer) (ctx : ScriptContext)
                           -> i ≢ Stop
                           -> (pf : agdaValidator par d i ctx ≡ true)
                           -> (getPar par oref tn ⊢ getS d ctx ~[ i ]~> getS' d ctx
                               × continuing ctx ≡ true
                               × checkTokenIn (d .fst) ctx ≡ true
                               × checkTokenOut (d .fst) ctx ≡ true )
validatorImpliesTransition par d (Update v r) ctx p1 p2
  = TUpdate (==to≡ (owner (snd d)) (sig ctx) (get (go (checkTokenIn (d .fst) ctx) p2)))
  (==vto≡ (newValue ctx) v (get (go (checkMinValue v) (go (checkRational r)
  (go (checkSigned (owner (snd d)) ctx) (go (checkTokenIn (d .fst) ctx) p2))))))
  (==dto≡ (get (go (newValue ctx == v) (go (checkMinValue v) (go (checkRational r)
  (go (checkSigned (owner (snd d)) ctx) (go (checkTokenIn (d .fst) ctx) p2)))))))
  (get (go (checkSigned (owner (snd d)) ctx) (go (checkTokenIn (d .fst) ctx) p2)))
  (get (go (checkRational r) (go (checkSigned (owner (snd d)) ctx)
  (go (checkTokenIn (d .fst) ctx) p2)))) , get (go
  (newDatum ctx == (d. fst , record {ratio = r ; owner = owner (snd d)}))
  (go (newValue ctx == v) (go (checkMinValue v) (go (checkRational r)
  (go (checkSigned (owner (snd d)) ctx) (go (checkTokenIn (d .fst) ctx) p2)))))) ,
  get p2 , go (continuing ctx)
  (go (newDatum ctx == (d. fst , record {ratio = r ; owner = owner (snd d)}))
  (go (newValue ctx == v) (go (checkMinValue v) (go (checkRational r)
  (go (checkSigned (owner (snd d)) ctx)
  (go (checkTokenIn (d .fst) ctx) p2))))))

validatorImpliesTransition {adr} {oref} record { sellCurr = sellC ; buyCurr = buyC } (tok , lab) (Exchange amt pkh) ctx p1 p2
  = TExchange (==vto≡ (newValue ctx + assetClassValue sellC amt) (oldValue ctx)
  (get (go (checkTokenIn tok ctx) p2)))
  (==dto≡ (get (go (newValue ctx + (assetClassValue sellC amt) == oldValue ctx) (go (checkTokenIn tok ctx) p2))))
  (get (get (go (newDatum ctx == (tok , lab)) (go (newValue ctx + (assetClassValue sellC amt) == oldValue ctx) (go (checkTokenIn tok ctx) p2)))))
  (go (ratioCompare amt (assetClassValueOf (getPayment (owner lab) ctx) buyC) (ratio lab))
  (get (go (newDatum ctx == (tok , lab)) (go (newValue ctx + (assetClassValue sellC amt) == oldValue ctx) (go (checkTokenIn tok ctx) p2))))) , get (go (checkPaymentRatio (owner lab) amt buyC (ratio lab) ctx) (go (newDatum ctx == (tok , lab))
  (go (newValue ctx + (assetClassValue sellC amt) == oldValue ctx) (go (checkTokenIn tok ctx) p2)))) , get p2 , go (continuing ctx) (go (checkPaymentRatio (owner lab) amt buyC (ratio lab) ctx) (go (newDatum ctx == (tok , lab))
  (go (newValue ctx + (assetClassValue sellC amt) == oldValue ctx) (go (checkTokenIn tok ctx) p2))))

{- refl
  (get (go (checkPaymentRatio (owner lab) amt buyC (ratio lab) ctx) (go (newDatum ctx == (tok , lab))
  (go (oldValue ctx == newValue ctx <> (assetClassValue sellC amt)) (go (checkTokenIn tok ctx) p2))))) (get p2)
  (go (continuing ctx) (go (checkPaymentRatio (owner lab) amt buyC (ratio lab) ctx) (go (newDatum ctx == (tok , lab))
  (go (oldValue ctx == newValue ctx <> (assetClassValue sellC amt)) (go (checkTokenIn tok ctx) p2))))) -}
validatorImpliesTransition par d Stop ctx p1 p2 = ⊥-elim (p1 refl)


-- Minting the token implies we are in the initial state of our model
mintingImpliesStart : ∀ {par} (adr : Address) (oref : TxOutRef) (tn : TokenName) (top : ⊤) (ctx : ScriptContext)
                           -> getMintedAmount ctx ≢ -1
                           -> (pf : agdaPolicy adr oref tn top ctx ≡ true)
                           -> (getPar par oref tn ⊢ getMintS tn ctx
                              × continuing ctx ≡ true
                              × getMintedAmount ctx ≡ 1
                              × checkTokenOut (newDatum ctx .fst) ctx ≡ true)
mintingImpliesStart adr oref tn top ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , lab) ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = mint' } p1 p2 with getMintedAmount ctx == -1 in eq
mintingImpliesStart adr oref tn top ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , lab) ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = mint' } p1 p2 | True rewrite ==ito≡ mint' (negsuc 0) eq = ⊥-elim (p1 refl) 
mintingImpliesStart adr oref rn top ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , lab) ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = mint' } p1 p2 | False with getMintedAmount ctx == 1 in eq'
mintingImpliesStart {record { sellCurr = sellC ; buyCurr = buyC }} adr oref tn top ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , lab) ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = mint' ; tokCurrSymbol = cs } p1 p2 | False | True rewrite sym (==tto≡ (cs , tn) tok (get (get (go (consumes oref ctx) (go (continuingAddr adr ctx) p2)))))
  = TStart refl (==to≡ oref inputRef (get (go (continues) p2))) refl (go (ownAssetClass tn ctx == tok) (get (go (consumes oref ctx) (go (continuingAddr adr ctx) p2)))) , get p2 , ==ito≡ mint' (+ 1) eq' , go (checkDatum adr tn ctx) (go (consumes oref ctx) (go (continuingAddr adr ctx) p2))

mintingImpliesStart adr oref tn top ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , lab) ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = mint' } p1 p2 | False | False = ⊥-elim (get⊥ (sym p2))

-- Validator returning true and burning a token implies we are in the terminal state 
bothImplyStop : ∀ (par : Params) (d : Datum) (adr : Address) (oref : TxOutRef) (tn : TokenName) (i : Redeemer) (ctx : ScriptContext)
               -> getMintedAmount ctx ≡ -1
               -> (agdaValidator par d i ctx && agdaPolicy adr oref tn tt ctx) ≡ true
               -> ( getPar par oref tn ⊢ getS d ctx ~[ i ]~| getS' d ctx
                  × continuing ctx ≡ false
                  × getMintedAmount ctx ≡ -1
                  × checkTokenIn (d .fst) ctx ≡ true )

{-
bothImplyStop par d@(tok , lab) adr oref tn i@(Update v r) ctx refl p2 with (continuing ctx)
...| True =  ⊥-elim (get⊥ (sym (go (agdaValidator par d i ctx) {!!})))
...| False = ⊥-elim (get⊥ (sym (go (newDatum ctx == (tok , record {ratio = r ; owner = owner lab})) (go (newValue ctx == v) (go (checkMinValue v) (go (checkRational r) (go (checkSigned (owner lab) ctx) (go (checkTokenIn tok ctx) (get p2)))))))))
bothImplyStop par d@(tok , lab) adr oref tn i@(Exchange amt pkh) ctx refl p2 with (continuing ctx)
...| True =  ⊥-elim (get⊥ (sym (go (agdaValidator par d i ctx) {!!})))
...| False = ⊥-elim (get⊥ (sym (go (checkPaymentRatio (owner lab) amt (buyCurr par) (ratio lab) ctx) (go (newDatum ctx == (tok , lab)) (go (oldValue ctx == newValue ctx <> (assetClassValue (sellCurr par) amt)) (go (checkTokenIn tok ctx) (get p2)))))))
bothImplyStop par d adr oref tn Stop ctx refl p2 = TStop (==to≡ (owner (snd d)) (sig ctx) (go (not (continuing ctx)) (go (checkTokenIn (d .fst) ctx) (get p2)))) , unNot (go (agdaValidator par d Stop ctx) p2) , refl , get (get p2)
-}
bothImplyStop par (tok , lab) adr oref tn (Update v r) ctx@record { continues = false } refl p2 = ⊥-elim (get⊥ (sym (go (newDatum ctx == (tok , record {ratio = r ; owner = owner lab})) (go (newValue ctx == v) (go (checkMinValue v) (go (checkRational r) (go (checkSigned (owner lab) ctx) (go (checkTokenIn tok ctx) (get p2)))))))))
bothImplyStop par d adr oref tn i@(Update v r) ctx@record { continues = true } refl p2 = ⊥-elim (get⊥ (sym (go (agdaValidator par d i ctx) p2)))
bothImplyStop par (tok , lab) adr oref tn (Exchange amt pkh) ctx@record { continues = false } refl p2 = ⊥-elim (get⊥ (sym (go (checkPaymentRatio (owner lab) amt (buyCurr par) (ratio lab) ctx) (go (newDatum ctx == (tok , lab)) (go (newValue ctx + (assetClassValue (sellCurr par) amt) == oldValue ctx) (go (checkTokenIn tok ctx) (get p2)))))))
bothImplyStop par d adr oref tn i@(Exchange amt pkh) ctx@record { continues = true } refl p2 =  ⊥-elim (get⊥ (sym (go (agdaValidator par d i ctx) p2)))
bothImplyStop par d adr oref tn Stop ctx refl p2 = TStop (==to≡ (owner (snd d)) (sig ctx) (go (not (continuing ctx)) (go (checkTokenIn (d .fst) ctx) (get p2)))) , unNot (go (agdaValidator par d Stop ctx) p2) , refl , get (get p2)


--Lemma for transition implies validation returns true
≡to==l : ∀ {a b : Label} -> a ≡ b -> (a == b) ≡ true
≡to==l {record { ratio = ratio ; owner = owner }} refl
  rewrite i=i (num ratio) | i=i (den ratio) | n=n owner = refl

-- Performing a transition implies that the validator returns true
transitionImpliesValidator : ∀ {oref tn} (par : Params) (d : Datum) (i : Redeemer) (ctx : ScriptContext)
                           -> (getPar par oref tn ⊢ getS d ctx ~[ i ]~> getS' d ctx
                              × continuing ctx ≡ true
                              × checkTokenIn (d .fst) ctx ≡ true
                              × checkTokenOut (d .fst) ctx ≡ true)
                           -> agdaValidator par d i ctx ≡ true
transitionImpliesValidator par d (Update v r) ctx ((TUpdate refl refl refl p4 p5) , refl , refl , refl )
  rewrite p4 | p5 | n=n (owner (d .snd)) | v=v v | t=t (d .fst) | i=i (num r) | i=i (den r) = refl 
transitionImpliesValidator record { sellCurr = sellC ; buyCurr = buyC } d (Exchange amt pkh) ctx ((TExchange refl refl p3 p4) , refl , refl , refl )
  rewrite p3 | p4 
    | v=v (newValue ctx + MkMap ((sellC , amt) ∷ [])) 
    | t=t (d .fst) | i=i (num (ratio (d .snd))) | i=i (den (ratio (d .snd))) 
    | n=n (owner (snd d)) = refl
    
-- Being in the initial model state implies we can mint a token
startImpliesMinting : ∀ {par} (adr : Address) (oref : TxOutRef) (tn : TokenName) (top : ⊤) (ctx : ScriptContext)
                           -> ( getPar par oref tn ⊢ getMintS tn ctx
                              × continuing ctx ≡ true
                              × getMintedAmount ctx ≡ 1
                              × checkTokenOut (newDatum ctx .fst) ctx ≡ true)
                           -> agdaPolicy adr oref tn top ctx ≡ true
startImpliesMinting {record { sellCurr = sellC ; buyCurr = buyC }} adr oref tn top ctx ((TStart refl refl refl p) , refl , refl , refl )
  rewrite t=t (ownAssetClass tn ctx) | n=n oref | p = refl
  
-- Getting to the terminal state implies that the validator returns true and a token can be burned
stopImpliesBoth : ∀ (par : Params) (d : Datum) (adr : Address) (oref : TxOutRef) (tn : TokenName) (i : Redeemer) (ctx : ScriptContext)
               -> (getPar par oref tn ⊢ getS d ctx ~[ i ]~| getS' d ctx
                  × continuing ctx ≡ false
                  × getMintedAmount ctx ≡ -1
                  × checkTokenIn (d .fst) ctx ≡ true)
               -> ((agdaValidator par d i ctx && agdaPolicy adr oref tn tt ctx) ≡ true)
stopImpliesBoth par d adr oref tn i ctx ((TStop refl) , refl , refl , refl ) rewrite n=n (owner (d .snd)) = refl

-- Defining the components for the equivalence relation between the model and the validator.

data Phase : Set where
  Initial  : Phase
  Running  : Phase
  Terminal : Phase

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


-- The equivalence relation
record _≈_ {A : Set} (f : A -> Bool) (R : A -> Set) : Set where
  field to   : ∀ {a} -> f a ≡ true -> R a
        from : ∀ {a} -> R a        -> f a ≡ true


-- If we mint exactly 1 token we are in the Initial Phase
-- If we burn a token and the input is Close, we are in the Terminal Phase
-- Otherwise we are in the Running Phase
Classifier : Argument -> Phase
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; red = red ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (+_ zero) } } = Running
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; red = red ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = +[1+ zero ] } } = Initial
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; red = red ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = +[1+ N.suc n ] } } = Running
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; red = red ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc (N.suc n)) } } = Running
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; red = (Update x x₁) ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc zero) } } = Running
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; red = (Exchange x x₁) ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc zero) } } = Running
Classifier record { par = par ; adr = adr ; oref = oref ; dat = dat ; red = Stop ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc zero) } } = Terminal

-- The Validator as a function returning a boolean
totalF : Argument -> Bool
totalF arg with Classifier arg
... | Initial  = agdaPolicy (arg .adr) (arg .oref) (arg .tn) tt (arg .ctx)
... | Running  = agdaValidator (arg .par) (arg .dat) (arg .red) (arg .ctx) 
... | Terminal = agdaValidator (arg .par) (arg .dat) (arg .red) (arg .ctx) &&
                 agdaPolicy (arg .adr) (arg .oref) (arg .tn) tt (arg .ctx)

-- The State Transition System as a relation
totalR : Argument -> Set
totalR arg with Classifier arg
... | Initial  = getPar (arg .par) (arg .oref) (arg .tn) ⊢ getMintS (arg .tn) (arg .ctx)
                × continuing (arg .ctx) ≡ true
                × getMintedAmount (arg .ctx) ≡ 1
                × checkTokenOutAddr (arg .adr) (ownAssetClass (arg .tn) (arg .ctx)) (arg .ctx) ≡ true
... | Running  = getPar (arg .par) (arg .oref) (arg .tn) ⊢ getS (arg .dat) (arg .ctx)  ~[ (arg .red) ]~> getS' (arg .dat) (arg .ctx)
  × continuing (arg .ctx) ≡ true
                × checkTokenIn (arg .dat .fst) (arg .ctx) ≡ true
                × checkTokenOut (arg .dat .fst) (arg .ctx) ≡ true
... | Terminal =  getPar (arg .par) (arg .oref) (arg .tn) ⊢ getS (arg .dat) (arg .ctx)  ~[ (arg .red) ]~| getS' (arg .dat) (arg .ctx)
                 × continuing (arg .ctx) ≡ false
                 × getMintedAmount (arg .ctx) ≡ -1
                 × checkTokenIn (arg .dat .fst) (arg .ctx) ≡ true

-- Lemma for when the input is Close
removeStop : ∀ (arg : Argument) -> (getMintedAmount (ctx arg) ≢ (negsuc zero))
               -> (agdaValidator (arg .par) (arg .dat) (arg .red) (arg .ctx) ≡ true)
               -> ( getPar (arg .par) (arg .oref) (arg .tn) ⊢ getS (arg .dat) (arg .ctx)  ~[ (arg .red) ]~> getS' (arg .dat) (arg .ctx)
                × continuing (arg .ctx) ≡ true
                × checkTokenIn (arg .dat .fst) (arg .ctx) ≡ true
                × checkTokenOut (arg .dat .fst) (arg .ctx) ≡ true )
removeStop record { par = par ; adr = adr ; oref = oref ; dat = dat ; red = (Update x x₁) ; ctx = ctx } p1 p2 = validatorImpliesTransition par dat (Update x x₁) ctx (λ ()) p2
removeStop record { par = par ; adr = adr ; oref = oref ; dat = dat ; red = (Exchange x x₁) ; ctx = ctx } p1 p2 = validatorImpliesTransition par dat (Exchange x x₁) ctx (λ ()) p2
removeStop record { par = par ; adr = adr ; oref = oref ; dat = dat ; red = Stop ; ctx = ctx } p1 p2 = ⊥-elim (p1 (==ito≡ (getMintedAmount ctx) (negsuc 0) (get (go (not (continuing ctx)) (go (checkTokenIn (fst dat) ctx) p2)))))

-- The Equivalence Proof
totalEquiv : totalF ≈ totalR
totalEquiv = record { to = λ { {arg@record { par = par ; adr = adr ; oref = oref ; dat = dat ; red = red ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (+_ zero) } }} x → removeStop arg (λ ()) x ;
                               {record { par = par ; adr = adr ; oref = oref ; tn = tn; dat = dat ; red = red ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = +[1+ zero ] } }} x → mintingImpliesStart {par} adr oref tn tt c (λ ()) x ;
                               {arg@record { par = par ; adr = adr ; oref = oref ; dat = dat ; red = red ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = +[1+ N.suc n ] } }} x → removeStop arg (λ ()) x ;
                               {arg@record { par = par ; adr = adr ; oref = oref ; dat = dat ; red = red ; ctx = record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc (N.suc n)) } }} x → removeStop arg (λ ()) x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; red = (Update a b) ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc zero) } }} x → validatorImpliesTransition par dat (Update a b) c (λ ()) x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; red = (Exchange a b) ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc zero) } }} x → validatorImpliesTransition par dat (Exchange a b) c (λ ()) x ;
                               {record { par = par ; adr = adr ; oref = oref ; tn = tn ; dat = dat ; red = Stop ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc zero) } }} x → bothImplyStop par dat adr oref tn Stop c refl x }
                    ; from = λ { {arg@record { par = par ; adr = adr ; oref = oref ; dat = dat ; red = red ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (+_ zero) } }} x → transitionImpliesValidator par dat red c x ;
                               {record { par = par ; adr = adr ; oref = oref ; tn = tn ; dat = dat ; red = red ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = +[1+ zero ] } }} x → startImpliesMinting {par} adr oref tn tt c x  ;
                               {arg@record { par = par ; adr = adr ; oref = oref ; dat = dat ; red = red ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = +[1+ N.suc n ] } }} x → transitionImpliesValidator par dat red c x ;
                               {arg@record { par = par ; adr = adr ; oref = oref ; dat = dat ; red = red ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc (N.suc n)) } }} x → transitionImpliesValidator par dat red c x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; red = (Update a b) ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc zero) } }} x → transitionImpliesValidator par dat (Update a b) c x ;
                               {record { par = par ; adr = adr ; oref = oref ; dat = dat ; red = (Exchange a b) ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc zero) } }} x → transitionImpliesValidator par dat (Exchange a b) c x ;
                               {record { par = par ; adr = adr ; oref = oref ; tn = tn ; dat = dat ; red = Stop ; ctx = c@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = outputDatum ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = (negsuc zero) } }} x → stopImpliesBoth par dat adr oref tn Stop c x } } 



onlyOwnerCanStop : ∀ (par : MParams) (s s' : State)
  -> s' .tsig ≢ s .datum .snd .owner
  -> ¬ (par ⊢ s ~[ Stop ]~> s')
onlyOwnerCanStop par s s' p1 ()
