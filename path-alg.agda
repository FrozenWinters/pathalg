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

refl-alg : ∀ {i} {A : UU i} {x y : A} (s : PathAlg x y) → IdAlg s s
refl-alg s = mk-id (refl (↯ s))

infixl 20 _·alg_
_·alg_ : ∀ {i} {A : UU i} {x y : A} {s t r : PathAlg x y} →
  IdAlg s t → IdAlg t r → IdAlg s r
_·alg_ p q = mk-id (id↯ p · id↯ q)

inv-alg : ∀ {i} {A : UU i} {x y : A} {s t : PathAlg x y} →
  IdAlg s t → IdAlg t s
inv-alg p = mk-id (inv (id↯ p))

↯-▷ : ∀ {i} {A : UU i} {x y z : A} (s : PathAlg x y) (a : PathSeg y z) →
  IdAlg (s ▷ a) (□ ▷ ⟨| s |⟩ ▷ a)
↯-▷ □ a = mk-id (inv (lrefl (↯-seg a)))
↯-▷ s@(_ ▷ _) a = mk-id (refl _)

_▷R_  : ∀ {i} {A : UU i} {x y z : A} {s t : PathAlg x y} →
  IdAlg s t → (a : PathSeg y z) → IdAlg (s ▷ a) (t ▷ a)
_▷R_ {s = s} {t = t} p a = ↯-▷ s a ·alg mk-id (id↯ p ·R (↯-seg a)) ·alg inv-alg (↯-▷ t a)

_▷L_ : ∀ {i} {A : UU i} {x y z : A} (s : PathAlg x y) {a b : PathSeg y z} →
  IdAlg (□ ▷ a) (□ ▷ b) → IdAlg (s ▷ a) (s ▷ b)
_▷L_ s {a = a} {b = b} p = ↯-▷ s a ·alg mk-id (↯ s ·L id↯ p) ·alg inv-alg (↯-▷ s b)

id-to-alg : ∀ {i} {A : UU i} {x y : A} {s t : PathAlg x y} (p : Id s t) → IdAlg s t
id-to-alg {x = x} {y = y} {s = s} p = tr (λ (r : PathAlg x y)  → IdAlg s r) p (refl-alg s)

