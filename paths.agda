{-# OPTIONS --without-K --exact-split  #-}

module paths where

open import basic-types public

-- Equality types

data Id {i} {A : UU i} : A → A → UU i where
  refl : (x : A) → Id x x

inv : ∀ {i} {A : UU i} {x y : A} →
  Id x y → Id y x
inv (refl x) = refl x

infixl 20 _·_
_·_ : ∀ {i} {A : UU i} {x y z : A} →
  Id x y → Id y z → Id x z
refl x · refl x = refl x

lrefl : ∀ {i} {A : UU i} {x y : A} (a : Id x y) →
  Id ((refl x) · a) a
lrefl (refl x) = refl (refl x)

rrefl : ∀ {i} {A : UU i} {x y : A} (a : Id x y) →
  Id (a · (refl y)) a
rrefl (refl x) = refl (refl x)

linv : ∀ {i} {A : UU i} {x y : A} (a : Id x y) →
  Id ((inv a) · a) (refl y)
linv (refl x) = refl (refl x)

rinv : ∀ {i} {A : UU i} {x y : A} (a : Id x y) →
  Id (a · (inv a)) (refl x)
rinv (refl x) = refl (refl x)

invinv : ∀ {i} {A : UU i} {x y : A} (a : Id x y) →
  Id (inv (inv a)) a
invinv (refl x) = refl (refl x)

inv-con : ∀ {i} {A : UU i} {x y z : A} (a : Id x y) (b : Id y z) →
  Id (inv (a · b)) ((inv b) · (inv a))
inv-con (refl x) (refl x) = refl (refl x)

assoc : ∀ {i} {A : UU i} {x y z w : A} {a : Id x y} {b : Id y z} {c : Id z w} →
  Id  (a · b · c) (a · (b · c))
assoc {a = refl x} {b = refl x} {c = refl x} = refl (refl x)

_·L_ : ∀ {i} {A : UU i} {x y : A} {z : A} {a b : Id y z} →
  (c : Id x y) → (Id a b) → Id (c · a) (c · b)
refl x ·L α = lrefl _ · α · inv (lrefl _)

_·R_ : ∀ {i} {A : UU i} {x y : A} {a b : Id x y} (α : Id a b) {z : A} (c : Id y z) →
  Id (a · c) (b · c)
α ·R (refl z) = rrefl _ · α · inv (rrefl _)

-- The Eckmann-Hilton argument

ptype : ∀ (i) → UU (lsuc i)
ptype (i) =  Σ (UU i) (λ A → A)

Ω : ∀ {i} → ptype i → ptype i
Ω (A , x) =  ((Id x x) , refl x)

_✯_ : ∀ {i} {A : UU i} {x y : A} {a b : Id x y} (α : Id a b) {z : A} {c d : Id y z} (β : Id c d) →
  Id (a · c) (b · d)
α ✯ β = (α ·R _) · (_ ·L β)

✯loop : ∀ {i} {A : UU i} {x : A} (α β : pr₁ (Ω (Ω (A , x)))) →
  Id (α ✯ β) (α · β)
✯loop {x = x} α β = (rrefl _ · lrefl _) ✯ (rrefl _ · lrefl _)

_✯'_ : ∀ {i} {A : UU i} {x y : A} {a b : Id x y} (α : Id a b) {z : A} {c d : Id y z} (β : Id c d) →
  Id (a · c) (b · d)
α ✯' β = (_ ·L β) · (α ·R _)

✯'loop : ∀ {i} {A : UU i} {x : A} (α β : pr₁ (Ω (Ω (A , x)))) →
  Id (α ✯' β) (β · α)
✯'loop {x = x} α β = (rrefl _ · lrefl _) ✯ (rrefl _ · lrefl _)

✯≡✯' : ∀ {i} {A : UU i} {x y : A} {a b : Id x y} (α : Id a b) {z : A} {c d : Id y z} (β : Id c d) →
  Id (α ✯ β) (α ✯' β)
✯≡✯' {x = x} {a = (refl x)} (refl (refl x)) {c = (refl x)} (refl (refl x)) = refl (refl (refl x))

EH : ∀ {i} {A : UU i} {x : A} (α β : pr₁ (Ω (Ω (A , x)))) →
  Id (α · β) (β · α)
EH α β = inv (✯loop _ _) · ✯≡✯' _ _ · ✯'loop _ _


-- Action of paths

ap : ∀ {i j} {A : UU i} {B : UU j} (f : A → B) {x y : A} →  Id x y → Id (f x) (f y)
ap f (refl x) = refl (f x)

ap-id : ∀ {i} {A : UU i} {x y : A} (a : Id x y) →
  Id (ap id a) a
ap-id (refl x) = refl (refl x)

ap-comp : ∀ {i j k} {A : UU i} {B : UU j} {C : UU k} (g : B → C) (f : A → B) {x y : A} (a : Id x y)→
  Id (ap (g ∘ f) a) (ap g (ap f a))
ap-comp g f (refl x) = refl (refl ((g ∘ f) x))

ap-con : ∀ {i j} {A : UU i} {B : UU j} (f : A → B) {x y z : A} (a : Id x y) (b : Id y z) →
  Id (ap f (a · b)) ((ap f a) · (ap f b))
ap-con f (refl x) (refl x) = refl (refl (f x))

ap-inv :  ∀ {i j} {A : UU i} {B : UU j} (f : A → B) {x y : A} (a : Id x y) →
  Id (ap f (inv a)) (inv (ap f a))
ap-inv f (refl x) = refl (refl (f x))

ap2 : ∀ {i j k} {A : UU i} {B : UU j} {C : UU k} (f : A → B → C) {x x' : A} {y y' : B} →
  Id x x' → Id y y' → Id (f x y) (f x' y')
ap2 f (refl x) (refl y) = refl (f x y)

-- Transport

tr : ∀ {i j} {A : UU i} (P : A → UU j) {x y : A} (a : Id x y) → P x → P y
tr P (refl x) u = u

tr-con :  ∀ {i j} {A : UU i} (P : A → UU j) {x y z : A} (a : Id x y) (b : Id y z) (u : P x) →
  Id (tr P (a · b) u) (tr P b (tr P a u))
tr-con P (refl x) (refl x) u = refl u

tr-back :  ∀ {i j k} {B : UU j} (P : B → UU k) {A : UU i} (f : A → B) {x y : A} (a : Id x y) (u : P (f x)) →
  Id (tr (P ∘ f) a u) (tr P (ap f a) u)
tr-back P f (refl x) u = refl u

tr-fiberwise :  ∀ {i j k} {A : UU i} {P : A → UU j} {Q : A → UU k} (f : (x : A) → (P x) → (Q x)) {x y : A} (a : Id x y) (u : P x) →
  Id (tr Q a (f x u)) (f y (tr P a u))
tr-fiberwise f (refl x) u = refl (f x u)

-- Depenent action of paths

Id-over :  ∀ {i j} {A : UU i} (P : A → UU j) {x y : A} (a : Id x y) (u : P x) (v : P y) → UU j
Id-over P a u v =  Id (tr P a u) v

apd : ∀ {i j} {A : UU i} {P : A → UU j} (f : (x : A) → P x) {x y : A} (a : Id x y) → Id-over P a (f x) (f y)
apd f (refl x) = refl (f x)

apd-con : ∀ {i j} {A : UU i} {P : A → UU j} (f : (x : A) → P x) {x y z : A} (a : Id x y) (b : Id y z) →
  Id (apd f (a · b)) (((tr-con P a b (f x)) · (ap (tr P b) (apd f a))) · (apd f b))
apd-con f (refl x) (refl x) = refl (refl (f x))

apd-comp : ∀ {i j k} {A : UU i} {B : UU j} {P : (x : B) → UU k} (g : (x : B) → (P x)) (f : A → B) {x y : A} (a : Id x y) →
  Id (apd (g ∘ f) a) ((tr-back P f a ((g ∘ f) x)) · (apd g (ap f a)))
apd-comp g f (refl x) = refl (refl ((g ∘ f) x))

apd-comp-d : ∀ {i j k} {A : UU i} {P : A → UU j} {Q : A → UU k} (g : (x : A) → (P x) → (Q x)) (f : (x : A) → (P x)) {x y : A} (a : Id x y)  →
  Id (apd (g ∘d f) a) ((tr-fiberwise g a (f x)) · (ap (g y) (apd f a)))
apd-comp-d g f (refl x) = refl (refl ((g ∘d f) x))

tr-const : ∀ {i j} {A : UU i} (B : UU j) {x y : A} (a : Id x y) (u : B) →
  Id-over (λ _ → B) a u u
tr-const B a u = apd (λ _ → u) a
