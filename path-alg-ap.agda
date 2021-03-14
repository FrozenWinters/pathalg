{-# OPTIONS --without-K --exact-split  #-}

module path-alg-ap where

open import path-alg

module _ {i} where
  data FunSeq : (A B : UU i) → UU (lsuc i) where
    □fun : {A : UU i} → FunSeq A A
    _◁∘_ : {A B C : UU i} → (B → C) → FunSeq A B → FunSeq A C

  ↯fun : {A B : UU i} → FunSeq A B → (A → B)
  ↯fun □fun = id
  ↯fun (f ◁∘ fs) = f ∘ ↯fun fs

  infixr 28 _▷⊚◁_
  _▷⊚◁_ : {A B : UU i} (fs : FunSeq A B) {x y : A} →
    PathSeg x y → PathSeg ((↯fun fs) x) ((↯fun fs) y)
  □fun ▷⊚◁ a = a
  (f ◁∘ fs) ▷⊚◁ a = f ⊚ (fs ▷⊚◁ a)

  ↯-▷⊚◁ : {A B : UU i} (fs : FunSeq A B) {x y : A} (a : PathSeg x y) →
    IdAlg (□ ▷ (fs ▷⊚◁ a)) (□ ▷ (↯fun fs) ⊚ a)
  ↯-▷⊚◁ □fun a = mk-id (inv (ap-id (↯-seg a)))
  ↯-▷⊚◁ (f ◁∘ fs) a = mk-id (ap (ap f) (id↯ (↯-▷⊚◁ fs a)) · (inv (ap-comp f (↯fun fs) (↯-seg a))))

  _▷∘◁_ : {A B C : UU i} → FunSeq B C → FunSeq A B → FunSeq A C
  □fun ▷∘◁ gs = gs
  (f ◁∘ fs) ▷∘◁ gs = f ◁∘ (fs ▷∘◁ gs)

module _ {i} {A B : UU i} where
  infixr 20 _⊚◁_
  _⊚◁_ : (f : A → B) {x y : A} → PathAlg x y → PathAlg (f x) (f y)
  f ⊚◁ □ = □
  f ⊚◁ s ▷ a = (f ⊚◁ s) ▷ (f ⊚ a)

  ↯-⊚◁ : (f : A → B) {x y : A} (s : PathAlg x y) →
    IdAlg (f ⊚◁ s) (□ ▷ f ⊚ ⟨| s |⟩)
  ↯-⊚◁ f {x = x} □ = mk-id (refl (refl (f x)))
  ↯-⊚◁ f (□ ▷ a) = mk-id (refl (ap f (↯-seg a)))
  ↯-⊚◁ f (s@(_ ▷ _) ▷ a) = mk-id ((id↯ (↯-⊚◁ f s) ·R ap f (↯-seg a)) · inv (ap-con f (↯ s) (↯-seg a)))
