{-# OPTIONS --without-K --exact-split  #-}

module path-alg-reflection where

open import path-alg-reasoning
open import Reflection
open import Reflection.Term
open import Reflection.Pattern
open import Data.String as String
open import Data.List as List

mirror-commands-alg : {pt : PathType} (rs : ReasoningSeq ptAlg pt) → Term → Term → TC Term
mirror-commands-seg : {pt : PathType} (rs : ReasoningSeq ptSeg pt) → Term → Term → TC Term
mirror-commands-funseq : {pt : PathType} (rs : ReasoningSeq ptFunSeq pt) → Term → Term → TC Term
mirror-commands-done : {pt : PathType} (rs : ReasoningSeq ptDone pt) → Term → Term → TC Term

mirror-commands-alg □R s t = return t
mirror-commands-alg (Zoom n m ::R rs) s t =
  do
    n' ← quoteTC n
    m' ← quoteTC m
    s-zoomed ← return (def (quote PathAlgOps.drop)
      (vArg n' ∷ vArg (def (quote PathAlgOps.take) (vArg m' ∷ vArg s ∷ [])) ∷ []))
    s-tail ← return (def (quote PathAlgOps.drop)
      (vArg n' ∷ vArg (def (quote PathAlgOps.drop) (vArg m' ∷ vArg s ∷ [])) ∷ []))
    tail-len ← return (def (quote PathAlgOps.length) [ vArg s-tail ])
    t-zoomed ← return (def (quote PathAlgOps.drop)
      (vArg n' ∷ vArg (def (quote PathAlgOps.drop-from-end) (vArg tail-len ∷ vArg t ∷ [])) ∷ []))
    mirror-commands-alg rs s-zoomed t-zoomed
mirror-commands-alg (Select n ::R rs) s t =
  do
    n' ← quoteTC n
    s-selected ← return (def (quote PathAlgOps.first)
      (vArg (def (quote PathAlgOps.drop) (vArg n' ∷ vArg s ∷ []))
      ∷ vArg (con (quote unit) []) ∷ []))
    t-selected ← return (def (quote PathAlgOps.first)
      (vArg (def (quote PathAlgOps.drop) (vArg n' ∷ vArg t ∷ []))
      ∷ vArg (con (quote unit) []) ∷ []))
    mirror-commands-seg rs s-selected t-selected

mirror-commands-seg □R s t = return t
mirror-commands-seg (SegUnder n ::R rs) s t = {!!}
mirror-commands-seg (FunsOver n ::R rs) s t = {!!}
mirror-commands-seg (UnderBracket ::R rs) s t = {!!}

mirror-commands-funseq = {!!}

mirror-commands-done = {!!}

macro
  mirror-test1-helper : ∀ {i} {A : UU i} {x : A} (a : Id x x) → Term → TC ⊤
  mirror-test1-helper a hole = do
    s ← quoteTC (□ ▸ a ▸ a ▸ a)
    t ← quoteTC (□ ▸ a ▸ inv a ▸ a ▸ a ▸ a)
    ans ←  mirror-commands-alg (Zoom 1 0 ::R □R) s t
    unify hole ans

mirror-test1 : ∀ {i} {A : UU i} {x : A} (a : Id x x) → _
mirror-test1 a = mirror-test1-helper a

macro
  mirror-test2-helper : ∀ {i} {A : UU i} (f : A → A) {x : A} (a : Id (f (f x)) (f (f x))) (b : Id x x) → Term → TC ⊤
  mirror-test2-helper f a b hole = do
    s ← quoteTC (□ ▸ a ▸ a ▷ (f ∘ f) ⊚ ⟨| □ ▸ b ▸ b ▸ b |⟩ ▸ a ▸ a)
    t ← quoteTC (□ ▸ a ▸ a ▷ (f ∘ f) ⊚ ⟨| □ ▸ b ▸ inv b ▸ b ▸ b ▸ b |⟩ ▸ a ▸ a)
    ans ← mirror-commands-alg (Select 2 ::R □R) s t
    unify hole ans

mirror-test2 : ∀ {i} {A : UU i} (f : A → A) {x : A} (a : Id (f (f x)) (f (f x))) (b : Id x x) → _
mirror-test2 f a b = mirror-test2-helper f a b

infix 11  _=∎
infixr 10 _=⟨↑_⟩_ _=⟨↓_⟩_ _=⟨↑_&_⟩_ _=⟨↓_&_⟩_

macro
  _=⟨↓_⟩_ : ∀ {i} {A : UU i} {x y : A} (s : PathAlg x y) (rs : ReasoningSeq ptAlg ptDone)
    {t w : PathAlg x y} (α : IdAlg t w) → Term → TC ⊤
  _=⟨↓_⟩_ {i} s rs {w = w} α goal = do
    τ ← quoteTC (IdAlg s w)
    w' ← quoteTC w
    s' ← quoteTC s
    rs' ← quoteTC rs
    α' ← quoteTC α
    t ← checkType
      (def (quote _·alg_)
        (vArg (def (quote reason-done)
          (vArg s'
          ∷ vArg rs'
          ∷ vArg (con (quote any-j) [ vArg unknown ]) ∷ []))
        ∷ vArg α' ∷ []))
      τ
    unify goal t

macro
  _=⟨↓_&_⟩_ : ∀ {i} {A : UU i} {x y : A} (s : PathAlg x y)  {pt : PathType} (rs : ReasoningSeq ptAlg pt)
    (req : reasoning-requierment s rs) {t w : PathAlg x y} (α : IdAlg t w) → Term → TC ⊤
  _=⟨↓_&_⟩_ s rs req {w = w} α goal = do
    τ ← quoteTC (IdAlg s w)
    β ← quoteTC (reason-alg s rs req)
    α' ← quoteTC α
    t ← checkType (def (quote _·alg_) (vArg β ∷ vArg α' ∷ [])) τ
    unify goal t

macro
  _=⟨↑_⟩_ : ∀ {i} {A : UU i} {x y : A} (s : PathAlg x y) (rs : ReasoningSeq ptAlg ptDone)
    {t w : PathAlg x y} (α : IdAlg t w) → Term → TC ⊤
  _=⟨↑_⟩_ s rs {t = t} {w} α goal = do
    τ ← quoteTC (IdAlg s w)
    t' ← quoteTC t
    rs' ← quoteTC rs
    α' ← quoteTC α
    t ← checkType
      (def (quote _·alg_)
        (vArg (def (quote inv-alg)
          [ vArg (def (quote reason-done)
            (vArg t'
            ∷ vArg rs'
            ∷ vArg (con (quote any-j) [ vArg unknown ]) ∷ [])) ])
        ∷ vArg α' ∷ []))
      τ
    unify goal t

macro
  _=⟨↑_&_⟩_ : ∀ {i} {A : UU i} {x y : A} (s : PathAlg x y) {pt : PathType} (rs : ReasoningSeq ptAlg pt)
    {t w : PathAlg x y} (req : reasoning-requierment t rs) (α : IdAlg t w) → Term → TC ⊤
  _=⟨↑_&_⟩_ s rs {t = t} {w} req α goal = do
    τ ← quoteTC (IdAlg s w)
    β ← quoteTC (reason-alg t rs req)
    α' ← quoteTC α
    t ← checkType (def (quote _·alg_) (vArg (def (quote inv-alg) [ vArg β ]) ∷ vArg α' ∷ [])) τ
    unify goal t

_=∎ : ∀ {i} {A : UU i} {x y : A} (s : PathAlg x y) → IdAlg s s
s =∎ = refl-alg s
