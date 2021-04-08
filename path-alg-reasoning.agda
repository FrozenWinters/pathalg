{-# OPTIONS --without-K --exact-split  #-}

module path-alg-reasoning where

open import path-alg
open import path-alg-concat
open import path-alg-ap

data PathType : UU lzero where
  ptAlg : PathType
  ptSeg : PathType
  ptFunSeq : PathType
  ptDone : PathType

record PathSpec {i} : UU (lsuc i) where
  constructor mk-path-spec
  field
    {A} : UU i
    x y : A

record FunSpec {i} : UU (lsuc i) where
  constructor mk-fun-spec
  field
    {A B} : UU i
    f : A → B

param-type : ∀ {i} → PathType →  UU (lsuc i)
param-type ptAlg = PathSpec
param-type  ptSeg = PathSpec
param-type  ptFunSeq = FunSpec
param-type  ptDone = Lift ⊤

path-type : ∀ {i} (pt : PathType) → param-type {i} pt → UU (lsuc i)
path-type ptAlg (mk-path-spec x y) = PathAlg x y
path-type ptSeg (mk-path-spec x y) = PathSeg x y
path-type ptFunSeq (mk-fun-spec {A} {B} f) = Σ (FunSeq A B) (λ fs → Id f (↯fun fs))
path-type ptDone _ = Lift ⊤

record Recognition {i} (src-pt trgt-pt : PathType) (src-params : param-type {i} src-pt)
                       (src-path : path-type src-pt src-params) : UU (lsuc i) where
  constructor mk-recognition
  field
    trgt-params : (param-type {i} trgt-pt)
    trgt-path : (path-type trgt-pt trgt-params)
    get-final : (path-type trgt-pt trgt-params) →  (path-type src-pt src-params)
    recognition : Id src-path (get-final trgt-path)

data ReasoningCommand : PathType → PathType → UU lzero where
  Zoom : ℕ → ℕ → ReasoningCommand ptAlg ptAlg
  Select : ℕ → ReasoningCommand ptAlg ptSeg
  SegUnder : ℕ → ReasoningCommand ptSeg ptSeg
  FunsOver : ℕ → ReasoningCommand ptSeg ptFunSeq
  CollapseFuns : ReasoningCommand ptFunSeq ptDone

infixr 30 _::R_
data ReasoningSeq : PathType → PathType → UU lzero where
  □R : {pt : PathType} → ReasoningSeq pt pt
  _::R_ : {pt1 pt2 pt3 : PathType} → ReasoningCommand pt1 pt2 → ReasoningSeq pt2 pt3 → ReasoningSeq pt1 pt3

reasoning-type-alg : ∀ {i} {A : UU i} {x y : A} {pt : PathType} →
  (s : PathAlg x y) → ReasoningSeq ptAlg pt → Maybe (Recognition ptAlg pt (mk-path-spec x y) s)
  
reasoning-type-seg : ∀ {i} {A : UU i} {x y : A} {pt : PathType} →
  (a : PathSeg x y) → ReasoningSeq ptSeg pt → Maybe (Recognition ptSeg pt (mk-path-spec x y) a)

reasoning-type-funseq : ∀ {i} {A B : UU i} {pt : PathType} →
  (fs : FunSeq A B) → ReasoningSeq ptFunSeq pt → Maybe (Recognition ptFunSeq pt (mk-fun-spec (↯fun fs)) (fs , refl _))

reasoning-type-done : ∀ {i} {pt : PathType} → ReasoningSeq ptDone pt →
  Maybe (Recognition {i} ptDone pt _ _)
reasoning-type-done □R = just (mk-recognition _ _ id (refl _))

reasoning-type-alg {x = x} {y} s □R = just (mk-recognition (mk-path-spec x y) s id (refl _))
reasoning-type-alg s (Zoom n m ::R rs) with goZoom s n m
... | mk-ZoomInfo {x'} {y'} initial middle final p with reasoning-type-alg middle rs
...   | nothing = nothing
...   | just (mk-recognition tp ti f pf) =
             just (mk-recognition tp ti (λ t → initial ⋈ ((f t) ⋈ final))
                                        (p · (ap (λ t → initial ⋈ (t ⋈ final)) pf)))
reasoning-type-alg s (Select n ::R rs) with goSelect s n
... | nothing = nothing
... | just (mk-SelectInfo initial middle final p) with reasoning-type-seg middle rs
...   | nothing = nothing
...   | just (mk-recognition tp ti f pf) =
             just (mk-recognition tp ti (λ t → initial ⋈ ((f t) ◁ final))
                                        (p · (ap (λ t → initial ⋈ (t ◁ final)) pf)))

reasoning-type-seg {x = x} {y} a □R = just (mk-recognition (mk-path-spec x y) a id (refl _))
reasoning-type-seg a (SegUnder n ::R rs) with goUnder a n
... | nothing = nothing
... | just (mk-UnderInfo fs b px py pa) with reasoning-type-seg b rs
...   | nothing = nothing
...   | just (mk-recognition tp ti f pf) =
             just (mk-recognition tp ti (λ t → inv px *SegL (fs ▷⊚ (f t)) *SegR py)
                                        (pa · ap (λ t → inv px *SegL (fs ▷⊚ t) *SegR py) pf))
reasoning-type-seg a (FunsOver n ::R rs) with goUnder a n
... | nothing = nothing
... | just (mk-UnderInfo fs {x} {y} b px py pa) with reasoning-type-funseq fs rs
...   | nothing = nothing
...   | just (mk-recognition tp ti f pf) =
             just (mk-recognition tp ti
                     (λ t → inv px *SegL
                       (ap (^ x) (pr₂ (f t)) *SegL (pr₁ (f t) ▷⊚ b) *SegR  inv (ap (^ y) (pr₂ (f t))))
                       *SegR py)
                     (pa · ap
                     (λ t → inv px *SegL
                       (ap (^ x) (pr₂ t) *SegL (pr₁ t ▷⊚ b) *SegR  inv (ap (^ y) (pr₂ t)))
                       *SegR py) pf)) -- path algebra go brr

reasoning-type-funseq {A = A} {B} fs □R = just (mk-recognition (mk-fun-spec (↯fun fs)) (fs , refl _) id (refl _))
reasoning-type-funseq {i} fs (CollapseFuns ::R rs) with reasoning-type-done {i} rs
... | nothing = nothing
... | just (mk-recognition tp ti f pf) =
           just (mk-recognition tp ti (λ u → (↯fun fs ∘◁ □fun , refl _)) {!collapseFuns fs!})
{-
back-type-alg : ∀ {i} {A : UU i} {x y : A} {pt : PathType}
  (s : PathAlg x y) (rs : ReasoningSeq ptAlg pt) (p : Is-just (reasoning-type-alg s rs))
  (q : (to-witness p)) → UU i

back-type-seg : ∀ {i} {A : UU i} {x y : A} {pt : PathType}
  (s : PathSeg x y) (rs : ReasoningSeq ptSeg pt) (p : Is-just (reasoning-type-seg s rs))
  (q : (to-witness p)) → UU i

back-type-funseq : ∀ {i} {A B : UU i} {pt : PathType}
  (fs : FunSeq A B) (rs : ReasoningSeq ptFunSeq pt) (p : Is-just (reasoning-type-funseq fs rs))
  (q : (to-witness p)) → UU i

open import Data.Maybe.Relation.Unary.Any using (Any) renaming (just to any-j)

back-type-alg s □R (any-j _) q = IdAlg s (pr₁ q)
back-type-alg s (Zoom n m ::R rs) p q = {!!}
back-type-alg s (Select n ::R rs) p q = {!!}

back-type-seg = {!!}

back-type-funseq = {!!}-}
