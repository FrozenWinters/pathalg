{-# OPTIONS --without-K --exact-split  #-}

module path-alg-ap where

open import path-alg

module _ {i} where
  infixr 30 _∘◁_
  data FunSeq : (A B : UU i) → UU (lsuc i) where
    □fun : {A : UU i} → FunSeq A A
    _∘◁_ : {A B C : UU i} → (B → C) → FunSeq A B → FunSeq A C

  ↯fun : {A B : UU i} → FunSeq A B → (A → B)
  ↯fun □fun = id
  ↯fun (f ∘◁ fs) = f ∘ ↯fun fs

  infixr 28 _▷⊚_
  _▷⊚_ : {A B : UU i} (fs : FunSeq A B) {x y : A} →
    PathSeg x y → PathSeg ((↯fun fs) x) ((↯fun fs) y)
  □fun ▷⊚ a = a
  (f ∘◁ fs) ▷⊚ a = f ⊚ (fs ▷⊚ a)

  ↯-▷⊚ : {A B : UU i} (fs : FunSeq A B) {x y : A} (a : PathSeg x y) →
    IdSeg (fs ▷⊚ a) (↯fun fs ⊚ a)
  ↯-▷⊚ □fun a = mk-seg-id (inv (ap-id (↯-seg a)))
  ↯-▷⊚ (f ∘◁ □fun) a = mk-seg-id (refl _)
  ↯-▷⊚ (f ∘◁ g ∘◁ □fun) a = mk-seg-id (inv (ap-comp f g (↯-seg a)))
  ↯-▷⊚ (f ∘◁ fs@(_ ∘◁ _ ∘◁ _)) a = mk-seg-id (ap (ap f) (id-seg↯ (↯-▷⊚ fs a)) · (inv (ap-comp f (↯fun fs) (↯-seg a))))

  _▷∘◁_ : {A B C : UU i} → FunSeq B C → FunSeq A B → FunSeq A C
  □fun ▷∘◁ gs = gs
  (f ∘◁ fs) ▷∘◁ gs = f ∘◁ (fs ▷∘◁ gs)

  _▷⊚R_ : {A B : UU i} (fs : FunSeq A B) {x y : A} {a b : PathSeg x y} →
    IdSeg a b → IdSeg (fs ▷⊚ a) (fs ▷⊚ b)
  □fun ▷⊚R p = p
  (f ∘◁ fs) ▷⊚R p = mk-seg-id (ap (ap f) (id-seg↯ (fs ▷⊚R p)))

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
      fs : FunSeq A B
      {x y} : A
      a : PathSeg x y
      px : Id (↯fun fs x) x'
      py : Id (↯fun fs y) y'
      pa : Id b ((inv px) *SegL fs ▷⊚ a *SegR py)

  private
    u-fs = UnderInfo.fs
    u-x = UnderInfo.x
    u-y = UnderInfo.y
    u-a = UnderInfo.a
    u-px = UnderInfo.px
    u-py = UnderInfo.py

  *SegL-lem : {A B : UU i} (f : A → B) {x y z : A} (a : Id x y) (b : PathSeg y z) →
    Id (f ⊚ (a *SegL b)) ((ap f a) *SegL (f ⊚ b))
  *SegL-lem f a b = inv (tr-fibrewise' (f ⊚_) (inv a) b) · tr-back (λ u → PathSeg u (f _)) f (inv a) (f ⊚ b)
    · ap (λ v → (tr (λ u → PathSeg u (f _)) v (f ⊚ b))) (ap-inv f a)

  *SegR-lem : {A B : UU i} (f : A → B) {x y z : A} (a : PathSeg x y) (b : Id y z) →
    Id (f ⊚ (a *SegR b)) ((f ⊚ a) *SegR (ap f b))
  *SegR-lem f a b = inv (tr-fibrewise' (f ⊚_) b a) · tr-back (PathSeg (f _)) f b (f ⊚ a)

  goUnder : {A : UU i} {x y : A} (a : PathSeg x y) (n : ℕ) → Maybe (UnderInfo a)
  goUnder a Z = just (mk-UnderInfo □fun a (refl _) (refl _) (refl _))
  goUnder (△ x) (S n) = nothing
  goUnder ⟨| x |⟩ (S n) = nothing
  goUnder (p-inv a) (S n) = nothing
  goUnder (f ⊚ a) (S n) with goUnder a n
  ... | nothing = nothing
  ... | just (mk-UnderInfo fs b px py pa) = just (mk-UnderInfo (f ∘◁ fs) b (ap f px) (ap f py)
                   (ap (f ⊚_) pa · *SegR-lem f (inv px *SegL fs ▷⊚ b) py
                   · ap (_*SegR ap f py) (*SegL-lem f (inv px) (fs ▷⊚ b) · ap (_*SegL (f ⊚ (fs ▷⊚ b))) (ap-inv f px))))

  replaceUnder : {A : UU i} {x y : A} {a : PathSeg x y} (info : UnderInfo a) {t : PathSeg (u-x info) (u-y info)} →
    IdSeg (u-a info) t → IdSeg a (inv (u-px info) *SegL ((u-fs info) ▷⊚ t) *SegR (u-py info))
  replaceUnder {a = b} (mk-UnderInfo fs a px py pa) p = pa *segL (inv px *seg'L (fs ▷⊚R p) *seg'R py)

  colapseOver : {A : UU i} {x y : A} {a : PathSeg x y} (info : UnderInfo a) →
    IdSeg a (inv (u-px info) *SegL ↯fun (u-fs info) ⊚ (u-a info) *SegR (u-py info))
  colapseOver (mk-UnderInfo fs a px py pa) = pa *segL (inv px *seg'L ↯-▷⊚ fs a *seg'R py)

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
  under-test3 f a  = id-seg↯ (colapseOver (under-test f a))
