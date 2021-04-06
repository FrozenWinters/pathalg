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
  PathAlg x y → ReasoningSeq ptAlg pt → Maybe (UU (lsuc i))
  
reasoning-type-seg : ∀ {i} {A : UU i} {x y : A} {pt : PathType} →
  PathSeg x y → ReasoningSeq ptSeg pt → Maybe (UU (lsuc i))

reasoning-type-funseq : ∀ {i} {A B : UU i} {pt : PathType} →
  FunSeq A B → ReasoningSeq ptFunSeq pt → Maybe (UU (lsuc i))

reasoning-type-done : ∀ {i} {pt : PathType} → ReasoningSeq ptDone pt → Maybe (UU (lsuc i))
reasoning-type-done □R = just (Lift ⊤)

reasoning-type-alg {x = x} {y} s □R = just (Σ (PathAlg x y) (λ t → IdAlg s t))
reasoning-type-alg s (Zoom n m ::R rs) with goZoom s n m
... | mk-ZoomInfo {x'} {y'} _ middle _ _ = reasoning-type-alg middle rs
reasoning-type-alg s (Select n ::R rs) with goSelect s n
... | nothing = nothing
... | just (mk-SelectInfo _ middle _ _) = reasoning-type-seg middle rs

reasoning-type-seg {x = x} {y} a □R = just (Σ (PathSeg x y) (λ b → IdSeg a b))
reasoning-type-seg a (SegUnder n ::R rs) with goUnder a n
... | nothing = nothing
... | just (mk-UnderInfo _ b _ _ _) = reasoning-type-seg b rs
reasoning-type-seg a (FunsOver n ::R rs) with goUnder a n
... | nothing = nothing
... | just (mk-UnderInfo fs _ _ _ _) = reasoning-type-funseq fs rs

reasoning-type-funseq {A = A} {B} fs □R = just (FunSeq A B)
reasoning-type-funseq fs (CollapseFuns ::R rs) = reasoning-type-done rs

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

back-type-funseq = {!!}
