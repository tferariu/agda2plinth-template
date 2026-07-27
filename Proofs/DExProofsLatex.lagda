\begin{code}
open import Validators.DExLatex
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

module Proofs.DExProofsLatex where

-- Model and proofs for the Limit Order Book Distributed Exchange contract

-- The States of the State Transition System
\end{code}

\newcommand\dexState{%
\begin{code}
record State : Set where
  field
    datum       : Datum
    value       : Value  
    outVal      : Value
    tsig        : PubKeyHash
    spends      : TxOutRef
    threadTokCS : CurrencySymbol
open State
\end{code}
}


\newcommand\dexMParams{%
\begin{code}
record MParams : Set where
    field
        uniqueId         : TxOutRef
        threadTokName    : TokenName
        sellCurr         : AssetClass
        buyCurr          : AssetClass
open MParams public
\end{code}
}


\newcommand\dexInitial{%
\begin{code}
data _⊢_ : MParams -> State -> Set where
  TStart : ∀ {par s l}
    -> datum s ≡ ((threadTokCS s , threadTokName par) , l)
    -> uniqueId par ≡ spends s 
    -> checkRational (ratio l) ≡ true
    -------------------
    -> par ⊢ s
\end{code}
}


\newcommand\dexUpdate{%
\begin{code}
data _⊢_~[_]~>_ : MParams -> State -> Redeemer -> State -> Set where
  TUpdate : ∀ {v r s s' par}
    -> owner (snd (datum s)) ≡ tsig s'
    -> value s' ≡ v 
    -> datum s' ≡ ((fst (datum s)) ,
                  (record { ratio = r ; owner = owner (snd (datum s)) })) 
    -> checkRational r ≡ true 
    -> geq v minValue ≡ true
    -------------------
    -> par ⊢ s ~[ (Update v r) ]~> s'
\end{code}
}


\newcommand\dexExchange{%
\begin{code}
  TExchange : ∀ {amt pkh s s' par}
    -> value s' + assetClassValue (sellCurr par) amt ≡ value s 
    -> datum s' ≡ datum s
    -> ratioCompare amt (assetClassValueOf (outVal s') (buyCurr par))
       (ratio (snd (datum s))) ≡ true
    -> geq (outVal s') minValue ≡ true
    -------------------
    -> par ⊢ s ~[ (Exchange amt pkh) ]~> s'
\end{code}
}


\newcommand\dexFinal{%
\begin{code}
data _⊢_~[_]~|_ : MParams -> State -> Redeemer -> State -> Set where
  TStop : ∀ {s s' par}
    -> owner (snd (datum s)) ≡ tsig s'
    -------------------
    -> par ⊢ s ~[ Stop ]~| s'
\end{code}
}

\begin{code}[hide]


-- Model paramets consisting of the combined parameters of the validator and minting policy


-- Transition Rules of the State Transition Model

-- Initial State Transition

    

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
    -------------------------
    -> par ⊢ s ~[ (is ++ [ i ]) ]~|* s''

-- State Validity Predicate
\end{code}

\newcommand\dexValid{%
\begin{code}
valid : State -> Set 
valid s = checkRational (ratio (snd (datum s))) ≡ true 
\end{code}
}
\begin{code}[hide]


validP : MParams -> Set
validP par = true ≡ true

--State Validity Invariant
\end{code}

\newcommand\dexValidity{%
\begin{code}
validStateInitial : ∀ {s par}
  -> par ⊢ s
  -> valid s
validStateInitial (TStart p1 p2 p3) rewrite p1 = p3

validStateTransition : ∀ {s s' : State} {i par}
  -> valid s
  -> par ⊢ s ~[ i ]~> s'
  -> valid s'
validStateTransition v (TUpdate p1 p2 refl p4 p5) = p4
validStateTransition v (TExchange p1 refl p3 p4) = v
\end{code}
}
\begin{code}[hide]


invariant = valid

--Liquidity (For any state that is valid and has valid parameters,
--there exists another state and some inputs such that we can transition
--there and have no value left in the contract)
\end{code}

\newcommand\dexLiquidity{%
\begin{code}
liquidity : ∀ (par : MParams) (s : State) 
          -> invariant s -> validP par
          -> ∃[ s' ] ∃[ is ] ((par ⊢ s ~[ is ]~|* s'))
liquidity par s p1 p2 = ⟨ s' , ⟨  Stop ∷ [] , (fin nil (TStop refl)) ⟩ ⟩
  where
    s' = record
          { datum = datum s
          ; value = emptyValue
          ; outVal = emptyValue
          ; tsig = owner (snd (datum s))
          ; spends = 0
          ; threadTokCS = 0 }
\end{code}
}

\begin{code}[hide]



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
              ; tsig = 0 
              ; spends = 0 
              ; threadTokCS = 0 }

-- Initial State when we mint the token and put the smart contract on the blockchain
getMintS : TokenName -> ScriptContext -> State
getMintS tn ctx = record
             { datum = newDatum ctx
             ; value = newValue ctx
             ; outVal = 0
             ; tsig = sig ctx
             ; spends = iRef ctx
             ; threadTokCS = ownCurrencySymbol ctx }

-- Resulting State for normal transitions
getS' : Datum -> ScriptContext -> State
getS' (tok , lab) ctx = record
             { datum = newDatum ctx
             ; value = newValue ctx
             ; outVal = getPayment (owner lab) ctx
             ; tsig = sig ctx
             ; spends = iRef ctx
             ; threadTokCS = tok .fst }

-- Getting the Model parameters from the parameters of the validator and minting policy
getPar : Params -> TxOutRef -> TokenName -> MParams
getPar record { sellCurr = sellC ; buyCurr = buyC } oref tn
  = record
      { uniqueId         = oref
      ; threadTokName    = tn 
      ; sellCurr         = sellC 
      ; buyCurr          = buyC }


-- Lemma for validator returning true implies transition
==Lto≡ : ∀ (l l' : Label)
       -> (l == l') ≡ true
       -> l ≡ l' 
==Lto≡ record { ratio = ratio ; owner = owner }
       record { ratio = ratio' ; owner = owner' } pf
  rewrite ==rto≡ {ratio} {ratio'} (get pf)
  | ==to≡ owner owner' (go (ratio == ratio') pf) = refl


==dto≡ : {a b : Datum} -> (a == b) ≡ true -> a ≡ b
==dto≡ {tok , l} {tok' , l'} p rewrite ==tto≡ tok tok' (get p)
  | ==Lto≡ l l' (go (tok == tok') p) = refl



--Validator returning true implies that we can perform a transition
validatorImpliesRunning : ∀ {oref tn} (par : Params) (d : Datum)
  (i : Redeemer) (ctx : ScriptContext)
  -> getMintedAmount ctx ≡ 0
  -> (pf : agdaValidator par d i ctx ≡ true)
  -> (getPar par oref tn ⊢ getS d ctx ~[ i ]~> getS' d ctx
     × continuing ctx ≡ true
     × checkTokenIn (d .fst) ctx ≡ true
     × checkTokenOut (d .fst) ctx ≡ true )

validatorImpliesRunning par d (Update v r) ctx p1 p2
  = TUpdate (==to≡ (owner (snd d)) (sig ctx) (get (go (checkTokenIn (d .fst) ctx) p2)))
  (==vto≡ (newValue ctx) v (get (go (geq v minValue) (go (checkRational r)
  (go (checkSigned (owner (snd d)) ctx) (go (checkTokenIn (d .fst) ctx) p2))))))
  (==dto≡ (get (go (newValue ctx == v) (go (geq v minValue) (go (checkRational r)
  (go (checkSigned (owner (snd d)) ctx) (go (checkTokenIn (d .fst) ctx) p2)))))))
  (get (go (checkSigned (owner (snd d)) ctx) (go (checkTokenIn (d .fst) ctx) p2)))
  (get (go (checkRational r) (go (checkSigned (owner (snd d)) ctx)
  (go (checkTokenIn (d .fst) ctx) p2)))) , get (go
  (newDatum ctx == (d. fst , record {ratio = r ; owner = owner (snd d)}))
  (go (newValue ctx == v) (go (geq v minValue) (go (checkRational r)
  (go (checkSigned (owner (snd d)) ctx) (go (checkTokenIn (d .fst) ctx) p2)))))) ,
  get p2 , go (continuing ctx)
  (go (newDatum ctx == (d. fst , record {ratio = r ; owner = owner (snd d)}))
  (go (newValue ctx == v) (go (geq v minValue) (go (checkRational r)
  (go (checkSigned (owner (snd d)) ctx)
  (go (checkTokenIn (d .fst) ctx) p2))))))

validatorImpliesRunning {adr} {oref} record { sellCurr = sellC ; buyCurr = buyC } (tok , lab) (Exchange amt pkh) ctx p1 p2
  = TExchange (==vto≡ (newValue ctx + assetClassValue sellC amt) (oldValue ctx)
  (get (go (checkTokenIn tok ctx) p2)))
  (==dto≡ (get (go (newValue ctx + (assetClassValue sellC amt) == oldValue ctx) (go (checkTokenIn tok ctx) p2))))
  (get (get (go (newDatum ctx == (tok , lab)) (go (newValue ctx + (assetClassValue sellC amt) == oldValue ctx) (go (checkTokenIn tok ctx) p2)))))
  (go (ratioCompare amt (assetClassValueOf (getPayment (owner lab) ctx) buyC) (ratio lab))
  (get (go (newDatum ctx == (tok , lab)) (go (newValue ctx + (assetClassValue sellC amt) == oldValue ctx) (go (checkTokenIn tok ctx) p2))))) , get (go (checkPaymentRatio (owner lab) amt buyC (ratio lab) ctx) (go (newDatum ctx == (tok , lab))
  (go (newValue ctx + (assetClassValue sellC amt) == oldValue ctx) (go (checkTokenIn tok ctx) p2)))) , get p2 , go (continuing ctx) (go (checkPaymentRatio (owner lab) amt buyC (ratio lab) ctx) (go (newDatum ctx == (tok , lab))
  (go (newValue ctx + (assetClassValue sellC amt) == oldValue ctx) (go (checkTokenIn tok ctx) p2))))

validatorImpliesRunning par (tok , lab) Stop ctx refl p2 = ⊥-elim (&&2false (checkTokenIn tok ctx) (not (continuing ctx)) p2)


-- Minting the token implies we are in the initial state of our model
mintingImpliesInitial : ∀ (par : Params) (adr : Address)
  (oref : TxOutRef) (tn : TokenName) (ctx : ScriptContext)
  -> getMintedAmount ctx ≡ 1
  -> (pf : agdaPolicy adr oref tn tt ctx ≡ true)
  -> (getPar par oref tn ⊢ getMintS tn ctx
      × continuing ctx ≡ true
      × getMintedAmount ctx ≡ 1
      × checkTokenOut (ownAssetClass tn ctx) ctx ≡ true)
mintingImpliesInitial record { sellCurr = sellC ; buyCurr = buyC } adr oref tn ctx@record { inputVal = inputVal ; outputVal = outputVal ; outputDatum = (tok , lab) ; signature = signature ; continues = continues ; inputRef = inputRef ; mint = mint' ; tokCurrSymbol = cs } p1 p2 rewrite p1 | sym (==tto≡ (cs , tn) tok (get (get (go (consumes oref ctx) (go (continuingAddr adr ctx) p2))))) = (TStart refl (==to≡ oref inputRef (get (go (continues) p2))) (go (ownAssetClass tn ctx == tok) (get (go (consumes oref ctx) (go (continuingAddr adr ctx) p2))))) , (get p2 , refl) , go (checkDatum adr tn ctx) (go (consumes oref ctx) (go (continuingAddr adr ctx) p2))


-- Validator returning true and burning a token implies we are in the terminal state 
bothImplyFinal : ∀ (par : Params) (d : Datum) (adr : Address)
  (oref : TxOutRef) (tn : TokenName) (i : Redeemer) (ctx : ScriptContext)
  -> getMintedAmount ctx ≡ -1
  -> (agdaValidator par d i ctx && agdaPolicy adr oref tn tt ctx) ≡ true
  -> (getPar par oref tn ⊢ getS d ctx ~[ i ]~| getS' d ctx
      × continuing ctx ≡ false
      × getMintedAmount ctx ≡ -1
      × checkTokenIn (d .fst) ctx ≡ true )

bothImplyFinal par (tok , lab) adr oref tn (Update v r) ctx@record { continues = false } refl p2 = ⊥-elim (get⊥ (sym (go (newDatum ctx == (tok , record {ratio = r ; owner = owner lab})) (go (newValue ctx == v) (go (geq v minValue) (go (checkRational r) (go (checkSigned (owner lab) ctx) (go (checkTokenIn tok ctx) (get p2)))))))))
bothImplyFinal par d adr oref tn i@(Update v r) ctx@record { continues = true } refl p2 = ⊥-elim (get⊥ (sym (go (agdaValidator par d i ctx) p2)))
bothImplyFinal par (tok , lab) adr oref tn (Exchange amt pkh) ctx@record { continues = false } refl p2 = ⊥-elim (get⊥ (sym (go (checkPaymentRatio (owner lab) amt (buyCurr par) (ratio lab) ctx) (go (newDatum ctx == (tok , lab)) (go (newValue ctx + (assetClassValue (sellCurr par) amt) == oldValue ctx) (go (checkTokenIn tok ctx) (get p2)))))))
bothImplyFinal par d adr oref tn i@(Exchange amt pkh) ctx@record { continues = true } refl p2 =  ⊥-elim (get⊥ (sym (go (agdaValidator par d i ctx) p2)))
bothImplyFinal par d adr oref tn Stop ctx refl p2 = TStop (==to≡ (owner (snd d)) (sig ctx) (go (not (continuing ctx)) (go (checkTokenIn (d .fst) ctx) (get p2)))) , unNot (go (agdaValidator par d Stop ctx) p2) , refl , get (get p2)



--Lemma for transition implies validation returns true
≡to==l : ∀ {a b : Label} -> a ≡ b -> (a == b) ≡ true
≡to==l {record { ratio = ratio ; owner = owner }} refl
  rewrite i=i (num ratio) | i=i (den ratio) | n=n owner = refl

-- Performing a transition implies that the validator returns true
runningImpliesValidator : ∀ {oref tn} (par : Params) (d : Datum)
  (i : Redeemer) (ctx : ScriptContext)
  -> (getPar par oref tn ⊢ getS d ctx ~[ i ]~> getS' d ctx
     × continuing ctx ≡ true
     × checkTokenIn (d .fst) ctx ≡ true
     × checkTokenOut (d .fst) ctx ≡ true)
  -> agdaValidator par d i ctx ≡ true
  
runningImpliesValidator par d (Update v r) ctx ((TUpdate refl refl refl p4 p5) , refl , p7 , p8 )
  rewrite p4 | p5 | n=n (owner (d .snd)) | v=v v | t=t (d .fst) | i=i (num r) | i=i (den r) | p7 | p8 = refl 
runningImpliesValidator record { sellCurr = sellC ; buyCurr = buyC } d (Exchange amt pkh) ctx ((TExchange refl refl p3 p4) , refl , p6 , p7 )
  rewrite p3 | p4 | p6 | p7
    | v=v (newValue ctx + assetClassValue sellC amt)
    | t=t (d .fst) | i=i (num (ratio (d .snd))) | i=i (den (ratio (d .snd))) 
    | n=n (owner (snd d)) = refl
    
-- Being in the initial model state implies we can mint a token
initialImpliesMinting : ∀ (par : Params) (adr : Address)
  (oref : TxOutRef) (tn : TokenName) (top : ⊤) (ctx : ScriptContext)
  -> (getPar par oref tn ⊢ getMintS tn ctx
     × continuing ctx ≡ true
     × getMintedAmount ctx ≡ 1
     × checkTokenOut (ownAssetClass tn ctx) ctx ≡ true)
  -> agdaPolicy adr oref tn top ctx ≡ true

initialImpliesMinting record { sellCurr = sellC ; buyCurr = buyC } adr oref tn top ctx ((TStart refl refl p3) , refl , refl , p6 )
  rewrite t=t (ownAssetClass tn ctx) | n=n oref | p3 | p6 = refl
  
-- Getting to the terminal state implies that the validator returns true and a token can be burned
finalImpliesBoth : ∀ {tn i} (par : Params) (d : Datum)
  (adr : Address) (oref : TxOutRef) (ctx : ScriptContext)
  -> (getPar par oref tn ⊢ getS d ctx ~[ i ]~| getS' d ctx
     × continuing ctx ≡ false
     × getMintedAmount ctx ≡ -1
     × checkTokenIn (d .fst) ctx ≡ true)
  -> ((agdaValidator par d i ctx && agdaPolicy adr oref tn tt ctx) ≡ true)

finalImpliesBoth par d adr oref ctx ((TStop refl) , refl , refl , p4 ) rewrite n=n (owner (d .snd)) | p4 = refl

-- Defining the components for the equivalence relation between the model and the validator.

data Phase : Set where
  Initial  : Phase
  Running  : Phase
  Final : Phase

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
-- If we burn a token and the input is Close, we are in the Final Phase
-- Otherwise we are in the Running Phase
classifier : Argument -> Phase
classifier record { ctx = record { mint = pos 1 } } = Initial
classifier record { ctx = record { mint = pos zero } } = Running
classifier _ = Final


-- The Validator as a function returning a boolean
totalF : Argument -> Bool
totalF arg with classifier arg
... | Initial  = agdaPolicy (arg .adr) (arg .oref) (arg .tn) tt (arg .ctx)
... | Running  = agdaValidator (arg .par) (arg .dat) (arg .red) (arg .ctx) 
... | Final = agdaValidator (arg .par) (arg .dat) (arg .red) (arg .ctx) &&
                 agdaPolicy (arg .adr) (arg .oref) (arg .tn) tt (arg .ctx)

-- The State Transition System as a relation
totalR : Argument -> Set
totalR arg with classifier arg
... | Initial  = getPar (arg .par) (arg .oref) (arg .tn) ⊢ getMintS (arg .tn) (arg .ctx)
                × continuing (arg .ctx) ≡ true
                × getMintedAmount (arg .ctx) ≡ 1
                × checkTokenOutAddr (arg .adr) (ownAssetClass (arg .tn) (arg .ctx)) (arg .ctx) ≡ true
... | Running  = getPar (arg .par) (arg .oref) (arg .tn) ⊢ getS (arg .dat) (arg .ctx)  ~[ (arg .red) ]~> getS' (arg .dat) (arg .ctx)
  × continuing (arg .ctx) ≡ true
                × checkTokenIn (arg .dat .fst) (arg .ctx) ≡ true
                × checkTokenOut (arg .dat .fst) (arg .ctx) ≡ true
... | Final =  getPar (arg .par) (arg .oref) (arg .tn) ⊢ getS (arg .dat) (arg .ctx)  ~[ (arg .red) ]~| getS' (arg .dat) (arg .ctx)
                 × continuing (arg .ctx) ≡ false
                 × getMintedAmount (arg .ctx) ≡ -1
                 × checkTokenIn (arg .dat .fst) (arg .ctx) ≡ true

-- Lemma for when the input is Close

-- The Equivalence Proof
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




\end{code}

\newcommand\dexOwnerCanStop{%
\begin{code}
onlyOwnerCanStop : ∀ (par : MParams) (s s' : State)
  -> s' .tsig ≢ s .datum .snd .owner
  -> ¬ (par ⊢ s ~[ Stop ]~> s')
onlyOwnerCanStop par s s' p1 ()
\end{code}
}

\newcommand\mDF{%
\begin{code}
deadlockFreedom : ∀ (s : State) (par : MParams)
          -> valid s
          -> ∃[ s' ] ∃[ i ] ((par ⊢ s ~[ i ]~> s') ⊎ (par ⊢ s ~[ i ]~| s'))
\end{code}
}

\newcommand\mDFp{%
\begin{code}
deadlockFreedom s par p = ⟨ s' , ⟨ Stop , (inj₂ (TStop refl)) ⟩ ⟩
  where
  s' = record
        { datum = (0 , 0) ,
          record { ratio = record { num = 0 ; den = 0 } ; owner = 0 }
        ; value = unMap []
        ; outVal = unMap []
        ; tsig = s .datum .snd .owner
        ; spends = 0
        ; threadTokCS = 0
        }
\end{code}
}
