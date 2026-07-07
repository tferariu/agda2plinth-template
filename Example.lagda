\begin{code}[hide]

open import Haskell.Prelude hiding (All)
open import Agda.Primitive
open import Lib
open import Value
open import Data.Product using (∃; ∃-syntax; proj₁; proj₂) renaming (_,_ to ⟨_,_⟩; _×_ to _xx_)

module Example where

\end{code}

\newcommand\exOne{%
\begin{code}
example : Integer -> Integer -> Integer
example a b = if a == b then a else b
\end{code}
}

\newcommand\exTwo{%
\begin{code}
example2 : PubKeyHash -> PubKeyHash -> PubKeyHash
example2 a b = if a == b then a else b
\end{code}
}

\newcommand\exPragma{%
\begin{code}
{-# COMPILE AGDA2HS example #-}
\end{code}
}

\newcommand\exEx{%
\begin{code}
{-# COMPILE AGDA2HS example2 #-}
\end{code}
}


\newcommand\exstuff{%
\begin{code}
MParams = Nat
State = Nat
data Redeemer : Set where
  DoSomething      : Redeemer
  Stop : Redeemer
OtherInfo = Nat
constraint1 : State -> Bool
constraint1 s = True
constraint2 : State -> Bool
constraint2 s = True
constraint3 : MParams -> Bool
constraint3 s = True
constraint4 : OtherInfo -> Bool
constraint4 s = True

iConstraints : MParams -> State -> Bool
iConstraints par s = True
fConstraints : MParams -> State -> State -> Bool
fConstraints par s s' = True

continues : State -> Bool
continues s = True

hasToken : State -> Bool
hasToken s = True

data _⊢_~[]~>_ : MParams -> State -> State -> Set
  where
  Binging : ∀ {par s s'}
\end{code}
}

\newcommand\exBoilerplate{%
\begin{code}
    -> continues s  ≡ True
    -> continues s' ≡ True
    -> hasToken s   ≡ True
    -> hasToken s'  ≡ True
\end{code}
}

\newcommand\exBingus{%
\begin{code}
    -------------------
    -> par ⊢ s ~[]~> s'
\end{code}
}




\newcommand\exRunning{%
\begin{code}
data _⊢_~[_]~>_ : MParams -> State -> Redeemer -> State -> Set
  where
  Running : ∀ {par s i s'}
    -> constraint1 s ≡ True
    -> constraint2 s' ≡ True
    -> constraint3 par ≡ True
    -------------------
    -> par ⊢ s ~[ i ]~> s'
\end{code}
}




\newcommand\exFinal{%
\begin{code}
data _⊢_~[_]~|_ : MParams -> State -> Redeemer -> State -> Set
  where
  Final : ∀ {par s i s'}
    -> fConstraints par s s' ≡ True
    -------------------
    -> par ⊢ s ~[ i ]~| s'
\end{code}
}


\newcommand\exInitial{%
\begin{code}
data _⊢_ : MParams -> State -> Set
  where
  Initial : ∀ {par s}
    -> iConstraints par s ≡ True
    -------------------
    -> par ⊢ s
\end{code}
}


\newcommand\exRunningOI{%
\begin{code}
data _⊢_~[_⨾_]~>_ : MParams -> State -> Redeemer
  -> OtherInfo -> State -> Set where
  Transition : ∀ {par s i oi s'}
    -> constraint1 s ≡ True
    -> constraint2 s' ≡ True
    -> constraint3 par ≡ True
    -> constraint4 oi ≡ True
    -------------------
    -> par ⊢ s ~[ i ⨾ oi ]~> s'
\end{code}
}

\newcommand\exMulti{%
\begin{code}
data _⊢_~[_]~*_ : MParams -> State -> List Redeemer -> State -> Set
  where
  nil : ∀ { par s }
    ----------------------
    -> par ⊢ s ~[ [] ]~* s

  cons : ∀ { par s s' s'' i is }
    -> ∃[ oi ] (par ⊢ s ~[ i ⨾ oi ]~> s')
    -> par ⊢ s' ~[ is ]~* s''
    -------------------------
    -> par ⊢ s ~[ (i ∷ is) ]~* s''
\end{code}
}

\newcommand\exAll{%
\begin{code}

data All {a b} {A : Type a} (B : A → Type b) : List A → Type (a ⊔ b) where
  instance
    allNil  : All B []
    allCons : ∀ {x xs} ⦃ i : B x ⦄ ⦃ is : All B xs ⦄ → All B (x ∷ xs)
\end{code}
}




 
