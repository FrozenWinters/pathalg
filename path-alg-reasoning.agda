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
path-type ptFunSeq (mk-fun-spec {A} {B} f) = FunSeq A B f
path-type ptDone _ = Lift Bool

data done-fibr (x y : Bool) : UU lzero where
  done-path : done-fibr x y

segment-type : ∀ {i} (pt : PathType) (param : param-type {i} pt) (s t : path-type pt param) → UU (lsuc i)
segment-type ptAlg _ s t = Lift (IdAlg s t)
segment-type ptSeg _ a b = Lift (IdSeg a b)
segment-type ptFunSeq (mk-fun-spec f) fs gs = IdFunSeq fs gs
segment-type ptDone _ s t = Lift (done-fibr (lower s) (lower t))

record Recognition {i} (src-pt trgt-pt : PathType) (src-params : param-type {i} src-pt)
                       (src-path : path-type src-pt src-params) : UU (lsuc i) where
  constructor mk-recognition
  field
    trgt-params : (param-type {i} trgt-pt)
    trgt-path : (path-type trgt-pt trgt-params)
    get-final : (path-type trgt-pt trgt-params) →  (path-type src-pt src-params)
    recognition : Id src-path (get-final trgt-path)
    reasoning : {t : path-type trgt-pt trgt-params} →
      segment-type trgt-pt trgt-params trgt-path t → segment-type src-pt src-params src-path (get-final t)

private
  trgt-params = Recognition.trgt-params
  trgt-path = Recognition.trgt-path
  get-final = Recognition.get-final
  recognition = Recognition.recognition
  reasoning =  Recognition.reasoning

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

reasoning-type-funseq : ∀ {i} {A B : UU i} {f : A → B} {pt : PathType} →
  (fs : FunSeq A B f) → ReasoningSeq ptFunSeq pt → Maybe (Recognition ptFunSeq pt (mk-fun-spec f) fs)

reasoning-type-done : ∀ {i} {pt : PathType} → ReasoningSeq ptDone pt →
  Maybe (Recognition {i} ptDone pt _ (lift true))
reasoning-type-done □R = just (mk-recognition _ _ id (refl _) id)

reasoning-type-alg {x = x} {y} s □R = just (mk-recognition (mk-path-spec x y) s id (refl _) id)
reasoning-type-alg s (Zoom n m ::R rs) with goZoom s n m
... | mk-ZoomInfo {x'} {y'} initial middle final p with reasoning-type-alg middle rs
...   | nothing = nothing
...   | just (mk-recognition tp ti f pf r) =
             just (mk-recognition tp ti
               (λ t → initial ⋈ ((f t) ⋈ final))
               (p · (ap (λ t → initial ⋈ (t ⋈ final)) pf))
               (λ q → lift (replaceZoom (mk-ZoomInfo initial middle final p) (lower (r q)))))
reasoning-type-alg s (Select n ::R rs) with goSelect s n
... | nothing = nothing
... | just (mk-SelectInfo initial middle final p) with reasoning-type-seg middle rs
...   | nothing = nothing
...   | just (mk-recognition tp ti f pf r) =
             just (mk-recognition tp ti
               (λ t → initial ⋈ ((f t) ◁ final))
               (p · (ap (λ t → initial ⋈ (t ◁ final)) pf))
               (λ q → lift (replaceSelect (mk-SelectInfo initial middle final p) (lower (r q)))))

reasoning-type-seg {x = x} {y} a □R = just (mk-recognition (mk-path-spec x y) a id (refl _) id)
reasoning-type-seg a (SegUnder n ::R rs) with goUnder a n
... | nothing = nothing
... | just (mk-UnderInfo fs b px py pa) with reasoning-type-seg b rs
...   | nothing = nothing
...   | just (mk-recognition tp ti f pf r) =
             just (mk-recognition tp ti
               (λ t → inv px *SegL (fs ▷⊚ (f t)) *SegR py)
               (pa · ap (λ t → inv px *SegL (fs ▷⊚ t) *SegR py) pf)
               (λ q → lift (replaceUnder (mk-UnderInfo fs b px py pa) (lower (r q)))))
reasoning-type-seg a (FunsOver n ::R rs) with goUnder a n
... | nothing = nothing
... | just (mk-UnderInfo fs {x} {y} b px py pa) with reasoning-type-funseq fs rs
...   | nothing = nothing
...   | just (mk-recognition tp ti f pf r) =
             just (mk-recognition tp ti
               (λ t → inv px *SegL ((f t) ▷⊚ b) *SegR py)
               (pa · ap (λ t → inv px *SegL (t ▷⊚ b) *SegR py) pf)
               (λ q → lift (replaceOver (mk-UnderInfo fs b px py pa) (r q))))

reasoning-type-funseq {A = A} {B} {f} fs □R = just (mk-recognition (mk-fun-spec f) fs id (refl _) id)
reasoning-type-funseq {i} {A} {B} {h} fs (CollapseFuns ::R rs) with reasoning-type-done {i} rs
... | nothing = nothing
... | just (mk-recognition tp ti f pf r) =
           just (mk-recognition tp ti
             (g ∘ f)
             (ap g pf)
             (λ q → l (lower (r q)))) where
             g : Lift {j = lsuc i} Bool →  path-type ptFunSeq (mk-fun-spec h)
             g (lift true) = fs
             g (lift false) = tr (FunSeq A B) (↯fun-lem fs) (↯fun fs ∘◁ □fun)
             l : {b : Bool} → done-fibr true b → IdFunSeq fs (g (lift b))
             l {false} _ = collapseFuns fs
             l {true} _ = refl-fun fs

make-reas-path : ∀ {i} {A : UU i} (f : A → A) {x : A} (a : Id x x) (b : Id (f (f x)) (f (f x))) →
  PathAlg  (f (f x)) (f (f x))
make-reas-path f a b = □ ▷ △ b ▷ △ b ▷ f ⊚ f ⊚ △ a ▷ △ b

reasoning-test :  ∀ {i} {A : UU i} (f : A → A) {x : A} (a : Id x x) (b : Id (f (f x)) (f (f x))) →
  Maybe (Recognition ptAlg ptDone (mk-path-spec (f (f x)) (f (f x))) (make-reas-path f a b))
reasoning-test f a b = reasoning-type-alg (make-reas-path f a b) (Select 2 ::R FunsOver 2 ::R CollapseFuns ::R □R)

reasoning-test2 :  ∀ {i} {A : UU i} (f : A → A) {x : A} (a : Id x x) (b : Id (f (f x)) (f (f x))) →
  Id (b · b · ap f (ap f a) · b) (b · b · ap (λ x → f (f x)) a · b)
reasoning-test2 f a b = id↯ (lower (reasoning (to-witness-T (reasoning-test f a b) _) (lift (done-path {true} {false}))))
