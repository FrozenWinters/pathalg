{-# OPTIONS --without-K --exact-split  #-}

module path-alg-ap where

open import path-alg

module _ {i} where
  infixr 30 _∘◁_
  data FunSeq : (A B : UU i) (f : A → B) → UU (lsuc i) where
    □fun : {A : UU i} → FunSeq A A id
    _∘◁_ : {A B C : UU i} {f : A → B} (g : B → C) → FunSeq A B f → FunSeq A C (g ∘ f)

  ↯fun : {A B : UU i} {f : A → B} → FunSeq A B f → (A → B)
  ↯fun □fun = id
  ↯fun (f ∘◁ fs) = f ∘ ↯fun fs

  ↯fun-lem : {A B : UU i} {f : A → B} → (fs : FunSeq A B f) → Id (↯fun fs) f
  ↯fun-lem  □fun = refl id
  ↯fun-lem (g ∘◁ fs) = ap (g ∘_) (↯fun-lem fs)

  infixr 28 _▷⊚_
  _▷⊚_ : {A B : UU i} {f : A → B} (fs : FunSeq A B f) {x y : A} →
    PathSeg x y → PathSeg (f x) (f y)
  □fun ▷⊚ a = a
  (f ∘◁ fs) ▷⊚ a = f ⊚ (fs ▷⊚ a)

  *SegL-lem : {A B : UU i} (f : A → B) {x y z : A} (a : Id x y) (b : PathSeg y z) →
    Id (f ⊚ (a *SegL b)) ((ap f a) *SegL (f ⊚ b))
  *SegL-lem f a b = inv (tr-fibrewise' (f ⊚_) (inv a) b) · tr-back (λ u → PathSeg u (f _)) f (inv a) (f ⊚ b)
    · ap (λ v → (tr (λ u → PathSeg u (f _)) v (f ⊚ b))) (ap-inv f a)

  *SegR-lem : {A B : UU i} (f : A → B) {x y z : A} (a : PathSeg x y) (b : Id y z) →
    Id (f ⊚ (a *SegR b)) ((f ⊚ a) *SegR (ap f b))
  *SegR-lem f a b = inv (tr-fibrewise' (f ⊚_) b a) · tr-back (PathSeg (f _)) f b (f ⊚ a)

  *Seg-conj-lem : {A B : UU i} (f : A → B) {x y z w : A} (b : PathSeg y z) (a : Id y x) (c : Id z w) →
    Id (f ⊚ (inv a *SegL b *SegR c)) (inv (ap f a) *SegL f ⊚ b *SegR (ap f c))
  *Seg-conj-lem f b a c =
    (*SegR-lem f (inv a *SegL b) c) · (ap (_*SegR (ap f c)) ((*SegL-lem f (inv a) b) · ap (_*SegL f ⊚ b) (ap-inv f a)))

  _⊚L_ : {A B : UU i} (f : A → B) {x y : A} {a b : PathSeg x y} (p : IdSeg a b) →
    IdSeg (f ⊚ a) (f ⊚ b)
  f ⊚L p = mk-seg-id (ap (ap f) (id-seg↯ p))

  

  ↯-▷⊚ : {A B : UU i} {f : A → B} (fs : FunSeq A B f) {x y : A} (a : PathSeg x y) →
    IdSeg (fs ▷⊚ a) (inv (ap (^ x) (↯fun-lem fs)) *SegL (↯fun fs ⊚ a) *SegR (ap (^ y) (↯fun-lem fs)))
  ↯-▷⊚ □fun a = mk-seg-id (inv (ap-id (↯-seg a)))
  ↯-▷⊚ (f ∘◁ □fun) a = mk-seg-id (refl _)
--  ↯-▷⊚ (f ∘◁ g ∘◁ □fun) a = mk-seg-id (inv (ap-comp f g (↯-seg a)))
  ↯-▷⊚ (f ∘◁ fs@(_ ∘◁ _)) {x} {y} a =
    ((f ⊚L (↯-▷⊚ fs a)) *segR (*Seg-conj-lem f (↯fun fs ⊚ a) (ap (^ x) (↯fun-lem fs)) (ap (^ y) (↯fun-lem fs)))
      *segR (ap (inv (ap f (ap (^ x) (↯fun-lem fs))) *SegL f ⊚ ↯fun fs ⊚ a *SegR_) (ap-eval f y  (↯fun-lem fs))
               · ap (λ b → inv b *SegL f ⊚ ↯fun fs ⊚ a *SegR (ap (^ y) (↯fun-lem (f ∘◁ fs)))) (ap-eval f x (↯fun-lem fs))))
      ·seg (inv (ap (^ x) (↯fun-lem (f ∘◁ fs)))
                *seg'L mk-seg-id (inv (ap-comp f (↯fun fs) (↯-seg a)))
                *seg'R ap (^ y) (↯fun-lem (f ∘◁ fs)))
  -- The termination checker is being annoying with three levels of unfolding

  _▷∘◁_ : {A B C : UU i} {g : B → C} {f : A → B} → FunSeq B C g → FunSeq A B f → FunSeq A C (g ∘ f)
  □fun ▷∘◁ gs = gs
  (f ∘◁ fs) ▷∘◁ gs = f ∘◁ (fs ▷∘◁ gs)

  _▷⊚R_ : {A B : UU i} {f : A → B} (fs : FunSeq A B f) {x y : A} {a b : PathSeg x y} →
    IdSeg a b → IdSeg (fs ▷⊚ a) (fs ▷⊚ b)
  □fun ▷⊚R p = p
  (f ∘◁ fs) ▷⊚R p = mk-seg-id (ap (ap f) (id-seg↯ (fs ▷⊚R p)))

  record IdFunSeq {A B : UU i} {f : A → B} (fs gs : FunSeq A B f) : UU (lsuc i) where
    constructor mk-fun-id
    field
      id-ap↯ : {x y : A} (a : PathSeg x y) → IdSeg (fs ▷⊚ a) (gs ▷⊚ a)

  id-ap↯ = IdFunSeq.id-ap↯

  refl-fun : {A B : UU i} {f : A → B} (fs : FunSeq A B f) → IdFunSeq fs fs
  refl-fun fs = mk-fun-id (λ a → refl-seg (fs ▷⊚ a))

  tr-fun-lem : {A B : UU i} {f g : A → B} (fs : FunSeq A B f) (p : Id f g) {x y : A} (a : PathSeg x y) →
    Id (tr (FunSeq A B) p fs ▷⊚ a) (inv (ap (^ x) p) *SegL (fs ▷⊚ a) *SegR (ap (^ y) p))
  tr-fun-lem fs (refl f) a = refl (fs ▷⊚ a)

  collapseFuns : {A B : UU i} {f : A → B} (fs : FunSeq A B f) →
    IdFunSeq fs (tr (FunSeq A B) (↯fun-lem fs) (↯fun fs ∘◁ □fun))
  collapseFuns fs = mk-fun-id λ a → ↯-▷⊚ fs a *segR inv (tr-fun-lem (↯fun fs ∘◁ □fun) (↯fun-lem fs) a)

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

module _ {i} where
  record UnderInfo {B : UU i} {x' y' : B} (b : PathSeg x' y') : UU (lsuc i) where
    constructor mk-UnderInfo
    field
      {A} : UU i
      {f} : A → B
      fs : FunSeq A B f
      {x y} : A
      a : PathSeg x y
      px : Id (f x) x'
      py : Id (f y) y'
      pa : Id b ((inv px) *SegL fs ▷⊚ a *SegR py)

  private
    u-A = UnderInfo.A
    u-f = UnderInfo.f
    u-fs = UnderInfo.fs
    u-x = UnderInfo.x
    u-y = UnderInfo.y
    u-a = UnderInfo.a
    u-px = UnderInfo.px
    u-py = UnderInfo.py

  goUnder : {A : UU i} {x y : A} (a : PathSeg x y) (n : ℕ) → Maybe (UnderInfo a)
  goUnder a Z = just (mk-UnderInfo □fun a (refl _) (refl _) (refl _))
  goUnder (△ x) (S n) = nothing
  goUnder ⟨| x |⟩ (S n) = nothing
  goUnder (p-inv a) (S n) = nothing
  goUnder (f ⊚ a) (S n) with goUnder a n
  ... | nothing = nothing
  ... | just (mk-UnderInfo fs b px py pa) = just (mk-UnderInfo (f ∘◁ fs) b (ap f px) (ap f py)
                   (ap (f ⊚_) pa · (*Seg-conj-lem f (fs ▷⊚ b) px py)))

  replaceUnder : {A : UU i} {x y : A} {a : PathSeg x y} (info : UnderInfo a) {t : PathSeg (u-x info) (u-y info)} →
    IdSeg (u-a info) t → IdSeg a (inv (u-px info) *SegL ((u-fs info) ▷⊚ t) *SegR (u-py info))
  replaceUnder {a = b} (mk-UnderInfo fs a px py pa) p = pa *segL (inv px *seg'L (fs ▷⊚R p) *seg'R py)

  replaceOver : {A : UU i} {x y : A} {a : PathSeg x y} (info : UnderInfo a) {gs : FunSeq (u-A info) A (u-f info)} →
    (p : IdFunSeq (u-fs info) gs) → IdSeg a (inv (u-px info) *SegL (gs ▷⊚ (u-a info)) *SegR (u-py info))
  replaceOver (mk-UnderInfo fs a px py pa) p = pa *segL (inv px *seg'L (id-ap↯ p a) *seg'R py)

  collapseOver : {A : UU i} {x y : A} {a : PathSeg x y} (info : UnderInfo a) →
    IdSeg a (inv (u-px info)
                 *SegL (tr (FunSeq (u-A info) A) (↯fun-lem (u-fs info)) (↯fun (u-fs info) ∘◁ □fun)) ▷⊚ u-a info
                 *SegR u-py info)
  collapseOver info = replaceOver info (collapseFuns (u-fs info))

  -- Tests

  under5 : {A : UU i} {x : A} (f : A → A) (a : Id x x) → PathSeg (f (f (f (f (f x))))) (f (f (f (f (f x)))))
  under5 f a = f ⊚ f ⊚ f ⊚ f ⊚ f ⊚ △ a

  under-test : {A : UU i} {x : A} (f : A → A) (a : Id x x) → UnderInfo (under5 f a)
  under-test f a = to-witness-T (goUnder (under5 f a) 5) unit

  lrefl-id-seg : {A : UU i} {x y : A} (a : Id x y) → IdSeg (△ a) ⟨| □ ▷ △ (refl x) ▷ △ a |⟩
  lrefl-id-seg a = mk-seg-id (inv (lrefl a))

  under-test2 : {A : UU i} {x : A} (f : A → A) (a : Id x x) →
    Id (ap f (ap f (ap f (ap f (ap f a))))) (ap f (ap f (ap f (ap f (ap f (refl x · a))))))
  under-test2 f a = id-seg↯ ((replaceUnder (under-test f a) (lrefl-id-seg a)))

  under-test3 : {A : UU i} {x : A} (f : A → A) (a : Id x x) →
    Id (ap f (ap f (ap f (ap f (ap f a))))) (ap (f ∘ f ∘ f ∘ f ∘ f) a)
  under-test3 f a  = id-seg↯ (collapseOver (under-test f a))

