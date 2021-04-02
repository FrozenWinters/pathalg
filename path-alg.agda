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

record IdSeg {i} {A : UU i} {x y : A} (a b : PathSeg x y) : UU i where
  constructor mk-seg-id
  field
    id-seg↯ : Id (↯-seg a) (↯-seg b)

id-seg↯ = IdSeg.id-seg↯

infixl 20 _*algL_  _*algR_ _*segL_  _*segR_  _*SegL_  _*SegR_ _*seg'L_  _*seg'R_

_*algL_ :  ∀ {i} {A : UU i} {x y : A} {s t r : PathAlg x y} →
  Id s t → IdAlg t r → IdAlg s r
a *algL p = _*L_ {P = IdAlg} a p

_*algR_ :  ∀ {i} {A : UU i} {x y : A} {s t r : PathAlg x y} →
  IdAlg s t → Id t r → IdAlg s r
p *algR a = _*R_ {P = IdAlg} p a

_*segL_ :  ∀ {i} {A : UU i} {x y : A} {a b c : PathSeg x y} →
  Id a b → IdSeg b c → IdSeg a c
p *segL q = _*L_ {P = IdSeg} p q

_*segR_ :  ∀ {i} {A : UU i} {x y : A} {a b c : PathSeg x y} →
  IdSeg a b → Id b c → IdSeg a c
p *segR q = _*R_ {P = IdSeg} p q

_*SegL_ :  ∀ {i} {A : UU i} {x y z : A} →
  Id x y → PathSeg y z → PathSeg x z
a *SegL b = _*L_ {P = PathSeg} a b

_*SegR_ :  ∀ {i} {A : UU i} {x y z : A} →
  PathSeg x y → Id y z → PathSeg x z
a *SegR b = _*R_ {P = PathSeg} a b

_*seg'R_ :  ∀ {i} {A : UU i} {x y z : A} {a b : PathSeg x y} →
  IdSeg a b → (c : Id y z) → IdSeg (a *SegR c) (b *SegR c)
p *seg'R refl _ = p

_*seg'L_ :  ∀ {i} {A : UU i} {x y z : A} {a b : PathSeg y z} →
  (c : Id x y) → IdSeg a b → IdSeg (c *SegL a) (c *SegL b)
refl _ *seg'L p = p


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

_▷R_ : ∀ {i} {A : UU i} {x y z : A} {s t : PathAlg x y} →
  IdAlg s t → (a : PathSeg y z) → IdAlg (s ▷ a) (t ▷ a)
_▷R_ {s = □} {t = t} p a = ↯-▷ □ a ·alg mk-id (id↯ p ·R (↯-seg a)) ·alg inv-alg (↯-▷ t a)
_▷R_ {s = s@(_ ▷ _)} {t = □} p a = mk-id (id↯ p ·R (↯-seg a)) ·alg  inv-alg (↯-▷ □ a)
_▷R_ {s = s@(_ ▷ _)} {t = t@(_ ▷ _)} p a = mk-id (id↯ p ·R _)

--↯-▷ s a ·alg mk-id (id↯ p ·R (↯-seg a)) ·alg inv-alg (↯-▷ t a)

_▷L_ : ∀ {i} {A : UU i} {x y z : A} (s : PathAlg x y) {a b : PathSeg y z} →
  IdAlg (□ ▷ a) (□ ▷ b) → IdAlg (s ▷ a) (s ▷ b)
_▷L_ s {a = a} {b = b} p = ↯-▷ s a ·alg mk-id (↯ s ·L id↯ p) ·alg inv-alg (↯-▷ s b)


