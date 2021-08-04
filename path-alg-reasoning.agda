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
param-type ptSeg = PathSpec
param-type ptFunSeq = FunSpec
param-type ptDone = Lift ⊤

path-type : ∀ {i} (pt : PathType) → param-type {i} pt → UU (lsuc i)
path-type ptAlg (mk-path-spec x y) = PathAlg x y
path-type ptSeg (mk-path-spec x y) = PathSeg x y
path-type ptFunSeq (mk-fun-spec {A} {B} f) = FunSeq A B f
path-type ptDone _ = Lift Bool

data done-fibr (x y : Bool) : UU lzero where
  done-path : done-fibr x y

segment-type : ∀ {i} (pt : PathType) (param : param-type {i} pt) (s t : path-type pt param) → UU (lsuc i)
segment-type ptAlg _ s t = IdAlg s t
segment-type ptSeg _ a b = IdSeg a b
segment-type ptFunSeq (mk-fun-spec f) fs gs = IdFunSeq fs gs
segment-type {i} ptDone _ s t = Lift (done-fibr (lower s) (lower t))

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
  UnderBracket : ReasoningCommand ptSeg ptAlg

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

open Maybe
               
reasoning-type-alg {x = x} {y} s □R =
  just (mk-recognition (mk-path-spec x y) s id (refl _) id)
reasoning-type-alg s (Zoom n m ::R rs) with goZoom s n m
... | mk-ZoomInfo {x'} {y'} initial middle final p = do
        mk-recognition tp ti f pf r ← reasoning-type-alg middle rs
        just (mk-recognition tp ti
          (λ t → initial ⋈ ((f t) ⋈ final))
          (p · (ap (λ t → initial ⋈ (t ⋈ final)) pf))
          (λ q → replaceZoom (mk-ZoomInfo initial middle final p) (r q)))
reasoning-type-alg s (Select n ::R rs) = do
  mk-SelectInfo initial middle final p ← goSelect s n
  mk-recognition tp ti f pf r ← reasoning-type-seg middle rs
  just (mk-recognition tp ti
    (λ t → initial ⋈ ((f t) ◁ final))
    (p · (ap (λ t → initial ⋈ (t ◁ final)) pf))
    (λ q → replaceSelect (mk-SelectInfo initial middle final p) (r q)))

reasoning-type-seg {x = x} {y} a □R =
  just (mk-recognition (mk-path-spec x y) a id (refl _) id)
reasoning-type-seg a (SegUnder n ::R rs) = do
  mk-UnderInfo fs b px py pa ← goUnder a n
  mk-recognition tp ti f pf r ← reasoning-type-seg b rs
  just (mk-recognition tp ti
    (λ t → inv px *SegL (fs ▷⊚ (f t)) *SegR py)
    (pa · ap (λ t → inv px *SegL (fs ▷⊚ t) *SegR py) pf)
    (λ q → replaceUnder (mk-UnderInfo fs b px py pa) (r q)))
reasoning-type-seg a (FunsOver n ::R rs) = do
  mk-UnderInfo fs {x} {y} b px py pa ← goUnder a n
  mk-recognition tp ti f pf r ← reasoning-type-funseq fs rs
  just (mk-recognition tp ti
    (λ t → inv px *SegL ((f t) ▷⊚ b) *SegR py)
    (pa · ap (λ t → inv px *SegL (t ▷⊚ b) *SegR py) pf)
    (λ q → replaceOver (mk-UnderInfo fs b px py pa) (r q)))
reasoning-type-seg a (UnderBracket ::R rs) = do
  mk-BracketInfo s p ← goBracket a
  mk-recognition tp ti f pf r ← reasoning-type-alg s rs
  just (mk-recognition tp ti
    (λ t → ⟨| f t |⟩)
    (p · ap (λ t → ⟨| t |⟩) pf)
    (λ q → replaceBracket (mk-BracketInfo s p) (r q)))
reasoning-type-funseq {A = A} {B} {f} fs □R =
  just (mk-recognition (mk-fun-spec f) fs id (refl _) id)
reasoning-type-funseq {i} {A} {B} {h} fs (CollapseFuns ::R rs) = do
  mk-recognition tp ti f pf r ← reasoning-type-done {i} rs
  just (mk-recognition tp ti
    (g ∘ f)
    (ap g pf)
    (λ q → l (lower (r q))))
  where
    g : Lift {j = lsuc i} Bool →  path-type ptFunSeq (mk-fun-spec h)
    g (lift true) = fs
    g (lift false) = tr (FunSeq A B) (↯fun-lem fs) (↯fun fs ∘◁ □fun)
    l : {b : Bool} → done-fibr true b → IdFunSeq fs (g (lift b))
    l {false} _ = collapseFuns fs
    l {true} _ = refl-fun fs

reason-done : ∀ {i} {A : UU i} {x y : A} (s : PathAlg x y) (rs : ReasoningSeq ptAlg ptDone) →
  (w : Is-just (reasoning-type-alg s rs)) →
  (segment-type ptAlg (mk-path-spec x y) s ((get-final (to-witness w)) (lift false)))
reason-done {i} s rs w with to-witness w
... | mk-recognition tp ti f pf r = r (lift (done-path {lower ti} {false}))

flat-segment-type : ∀ {i} (pt : PathType) (param : param-type {i} pt) (s t : path-type pt param) → UU i
flat-segment-type ptAlg _ s t = Id (↯ s) (↯ t)
flat-segment-type ptSeg _ a b = Id (↯-seg a) (↯-seg b)
flat-segment-type ptFunSeq _ _ -  = Lift ⊥
flat-segment-type {i} ptDone _ s t = Lift (done-fibr (lower s) (lower t))

reasoning-requierment : ∀ {i} {A : UU i} {pt : PathType} {x y : A}
  (s : PathAlg x y) (rs : ReasoningSeq ptAlg pt) → UU (lsuc i)
reasoning-requierment {pt = pt} s rs with reasoning-type-alg s rs
... | nothing = Lift ⊥
... | just (mk-recognition tp ti f pf r) = Σ (path-type pt tp) (λ t → flat-segment-type pt tp ti t)

reasoning-conclusion : ∀ {i} {A : UU i} {pt : PathType} {x y : A}
  (s : PathAlg x y) (rs : ReasoningSeq ptAlg pt) → (req : reasoning-requierment s rs) → UU (lsuc i)
reasoning-conclusion {pt = pt} {x} {y} s rs req with reasoning-type-alg s rs
... | nothing = Lift ⊥
... | just (mk-recognition tp ti f pf r) = segment-type ptAlg (mk-path-spec x y) s (f (pr₁ req))

reason-alg : ∀ {i} {A : UU i} {pt : PathType} {x y : A} (s : PathAlg x y) (rs : ReasoningSeq ptAlg pt)
  (req : reasoning-requierment s rs) → reasoning-conclusion s rs req
reason-alg {pt = pt} s rs req with reasoning-type-alg s rs
reason-alg {pt = ptAlg} s rs req | just (mk-recognition tp ti f pf r) = r (mk-id (pr₂ req))
reason-alg {pt = ptSeg} s rs req | just (mk-recognition tp ti f pf r) = r (mk-seg-id (pr₂ req))
reason-alg {pt = ptDone} s rs req | just (mk-recognition tp ti f pf r) = r (lift (lower (pr₂ req)))

reasoning-test :  ∀ {i} {A : UU i} (f : A → A) {x : A} (a : Id x x) (b : Id (f (f x)) (f (f x))) →
  Id (b · b · ap f (ap f a) · b) (b · b · ap (f ∘ f) a · b)
reasoning-test {i} f a b =
  id↯ (reason-done (□ ▷ △ b ▷ △ b ▷ f ⊚ f ⊚ △ a ▷ △ b) (Select 2 ::R FunsOver 2 ::R CollapseFuns ::R □R) (any-j _))

reasoning-test2 : ∀ {i} {A : UU i} {x : A} (a b : Id x x) →
  Id (a · a · a · a) (a · a · b · inv b · a · a)
reasoning-test2 a b =
  id↯ (reason-alg (□ ▷ △ a ▷ △ a ▷ △ a ▷ △ a) (Zoom 2 0 ::R □R) (□ ▷ △ b ▷ △ inv b , inv (rinv b)))

reasoning-test3 : ∀ {i} {A : UU i} (f : A → A) {x : A} (a : Id (f (f x)) (f (f x))) (b : Id x x) →
  Id (a · a · ap f (ap f (b · b · b)) · a · a) (a · a · ap f (ap f (b · inv b · b · b · b)) · a · a)
reasoning-test3 f a b =
  id↯ (reason-alg (□ ▷ △ a ▷ △ a  ▷ f ⊚ f ⊚ ⟨| □ ▷ △ b ▷ △ b ▷ △ b |⟩ ▷ △ a ▷ △ a)
                  (Select 2 ::R SegUnder 2 ::R UnderBracket ::R Zoom 1 0 ::R □R)
                  (□ ▷ △ inv b ▷ △ b , inv (linv b)))
