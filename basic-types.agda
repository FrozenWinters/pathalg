{-# OPTIONS --without-K --exact-split #-}

module basic-types where

-- Universes

open import Agda.Primitive using (Level; lzero; lsuc; _⊔_) public

UU : ∀ (i) → Set (lsuc i)
UU i = Set i

record Lift {i j} (A : UU i) : UU (i ⊔ j) where
  constructor lift
  field lower : A

lower = Lift.lower

-- Function types

id : ∀ {i} {A : UU i} → A → A
id x = x

infixr 20 _∘_
_∘_ : ∀ {i j k} {A : UU i} {B : UU j} {C : B → UU k} →
  ((y : B) → (C y)) → (f : A → B) → ((x : A) → (C (f x)))
(g ∘ f) x = g (f x)

infixr 20 _∘d_
_∘d_ : ∀ {i j k} {A : UU i} {B : A → UU j} {C : (x : A) → (B x) → UU k} →
  ((x : A) → (y : (B x)) → (C x y)) → (f : (x : A) → (B x)) → ((x : A) → (C x (f x)))
(g ∘d f) x =  g x (f x)

^ : ∀ {i} {A : UU i} → A → ∀ {j} {B : UU j} (f : A → B) → B
(^ a) f = f a

-- Dependent Sums

record Σ {i j} (A : UU i) (B : A → UU j) : UU (i ⊔ j) where
  constructor _,_
  field
    pr₁ : A
    pr₂ : (B pr₁)

infix 0 _,_
pr₁ = Σ.pr₁
pr₂ = Σ.pr₂

-- Cartesian Products

_×_ : ∀ {i j} (A : UU i) (B : UU j) → UU (i ⊔ j)
A × B = Σ A (λ (_ : A) → B)

-- Coproducts

data _+_ {i j} (A : UU i) (B : UU j) : UU (i ⊔ j) where
  inl : A → A + B
  inr : B → A + B

-- Natural Numbers

open import Data.Nat as ℕ using (ℕ) renaming (zero to Z; suc to S) public

-- Unit type

open import Data.Unit as ⊤ using (⊤) renaming (tt to unit) public

-- Empty type

open import Data.Empty as ⊥ public

¬ : ∀ {i} (A : UU i) → UU i
¬ A = A → ⊥

-- Booleans

open import Data.Bool using (Bool; true; false) public

-- Empty type

open import Data.Empty public

-- Maybe

open import Data.Maybe as Maybe using (Maybe; just; nothing; maybe; to-witness; to-witness-T; Is-just; Is-nothing) public
open import Data.Maybe.Categorical public
open import Data.Maybe.Relation.Unary.Any using (Any) renaming (just to any-j) public
