{-# OPTIONS --without-K --exact-split  #-}

module path-alg where

open import paths public

data PathSeg {i} : {A : UU i} →  A → A → UU (lsuc i)

infixl 30 _▷_
data PathAlg {i} : {A : UU i} → A → A → UU (lsuc i) where
  □ : {A : UU i} {x : A} → PathAlg x x
  _▷_ : {A : UU i} {x y z : A} → PathAlg x y → PathSeg y z → PathAlg x z

infixr 31 △_ p-inv_ _⊚_
data PathSeg {i} where
   △_ : {A : UU i} {x y : A} → Id x y → PathSeg x y
   ⟨|_|⟩ : {A : UU i} {x y : A} → PathAlg x y → PathSeg x y
   p-inv_ : {A : UU i} {x y : A} → PathSeg x y → PathSeg y x
   _⊚_ : {A B : UU i} (f : A → B) {x y : A} → PathSeg x y → PathSeg (f x) (f y)

↯ : ∀ {i} {A : UU i} {x y : A} → PathAlg x y → Id x y
↯-seg : ∀ {i} {A : UU i} {x y : A} → PathSeg x y → Id x y

↯ {x = x} □ = refl x
↯ (□ ▷ a) = ↯-seg a
↯ (s ▷ a ▷ b) = ↯ (s ▷ a) · ↯-seg b

↯-seg (△ a) = a
↯-seg ⟨| s |⟩ = ↯ s
↯-seg (p-inv s) = inv (↯-seg s)
↯-seg (f ⊚ s) = ap f (↯-seg s)

record IdAlg {i} {A : UU i} {x y : A} (s t : PathAlg x y) : UU i where
  constructor mk-id
  field
    id↯ : Id (↯ s) (↯ t)

id↯ = IdAlg.id↯
