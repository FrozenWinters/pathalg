{-# OPTIONS --without-K --exact-split  #-}

module path-alg where

open import paths public

-- Agda won't let me do this
{-
data PathAlg : ∀ {i} {A : UU i} →  A → A → UU i  where
  △_ : ∀ {i} {A : UU i} {x y : A} → Id x y → PathAlg x y
  □ :  ∀ {i} {A : UU i} {x : A} → PathAlg x x
  _▷_ : ∀ {i} {A : UU i} {x y z : A} → PathAlg x y → PathAlg y z → PathAlg x z
  p-inv : ∀ {i} {A : UU i} {x y : A} → PathAlg x y → PathAlg y x
  _⊚_ : ∀ {i j} {A : UU i} {B : UU j} (f : A → A) {x y : A} → PathAlg x y → PathAlg (f x) (f y)
-}

data PathSeg {i} {A : UU i} : A → A → UU i

infixl 30 _▷_
data PathAlg {i} {A : UU i} : A → A → UU i where
  □ : {x : A} → PathAlg x x
  _▷_ : {x y z : A} → PathAlg x y → PathSeg y z → PathAlg x z

infixr 31 △_ p-inv_ _⊚_
data PathSeg {i} {A} where
   △_ : {x y : A} → Id x y → PathSeg x y
   ⟨|_|⟩ : {x y : A} → PathAlg x y → PathSeg x y
   p-inv_ : {x y : A} → PathAlg x y → PathSeg y x
   _⊚_ : (f : A → A) {x y : A} → PathAlg x y → PathSeg (f x) (f y)

↯ : ∀ {i} {A : UU i} {x y : A} → PathAlg x y → Id x y
↯-seg : ∀ {i} {A : UU i} {x y : A} → PathSeg x y → Id x y

↯ {x = x} □ = refl x
↯ (□ ▷ a) = ↯-seg a
↯ (s ▷ a ▷ b) = ↯ (s ▷ a) · ↯-seg b

↯-seg (△ a) = a
↯-seg ⟨| s |⟩ = ↯ s
↯-seg (p-inv s) = inv (↯ s)
↯-seg (f ⊚ s) = ap f (↯ s)
