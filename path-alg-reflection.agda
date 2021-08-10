{-# OPTIONS --without-K --exact-split  #-}

module path-alg-reflection where

open import path-alg-reasoning
open import Reflection
open import Reflection.Term
open import Reflection.Pattern
open import Data.String as String
open import Data.List as List

op-under : (accessor : Name) (former : Name) (args : List (Arg Term)) → Term
op-under accessor former args =
  (def accessor
    [ vArg (def (quote to-witness-T)
      (vArg (def former args) ∷ vArg (con (quote unit) []) ∷ [])) ])

mirror-commands-alg : {pt : PathType} (rs : ReasoningSeq ptAlg pt) → Term → Term → TC Term
mirror-commands-seg : {pt : PathType} (rs : ReasoningSeq ptSeg pt) → Term → Term → TC Term
mirror-commands-funseq : {pt : PathType} (rs : ReasoningSeq ptFunSeq pt) → Term → Term → TC Term
mirror-commands-done : {pt : PathType} (rs : ReasoningSeq ptDone pt) → Term → Term → TC Term

mirror-commands-alg □R s t = return t
mirror-commands-alg (Zoom n m ::R rs) s t = do
  n' ← quoteTC n
  m' ← quoteTC m
  let s-zoomed = (def (quote PathAlgOps.drop) (vArg n' ∷ vArg (def (quote PathAlgOps.take) (vArg m' ∷ vArg s ∷ [])) ∷ []))
  let s-tail = (def (quote PathAlgOps.drop) (vArg n' ∷ vArg (def (quote PathAlgOps.drop) (vArg m' ∷ vArg s ∷ [])) ∷ []))
  let tail-len = (def (quote PathAlgOps.length) [ vArg s-tail ])
  let t-zoomed = (def (quote PathAlgOps.drop) (vArg n' ∷ vArg (def (quote PathAlgOps.drop-from-end) (vArg tail-len ∷ vArg t ∷ [])) ∷ []))
  ans ← mirror-commands-alg rs s-zoomed t-zoomed
  normalise ans
mirror-commands-alg (Select n ::R rs) s t = do
  n' ← quoteTC n
  let s-selected = op-under (quote SelectInfo.middle) (quote goSelect) (vArg s ∷ vArg n' ∷ [])
  let t-selected = op-under (quote SelectInfo.middle) (quote goSelect) (vArg t ∷ vArg n' ∷ [])
  ans ← mirror-commands-seg rs s-selected t-selected
  normalise ans

mirror-commands-seg □R s t = return t
mirror-commands-seg (SegUnder n ::R rs) s t = do
  n' ← quoteTC n
  let s-under = op-under (quote UnderInfo.a) (quote goUnder) (vArg s ∷ vArg n' ∷ [])
  let t-under = op-under (quote UnderInfo.a) (quote goUnder) (vArg t ∷ vArg n' ∷ [])
  ans ← mirror-commands-seg rs s-under t-under
  normalise ans
mirror-commands-seg (FunsOver n ::R rs) s t = return (quoteTerm ℕ) -- TODO
mirror-commands-seg (UnderBracket ::R rs) s t = do
  let s-under = op-under (quote BracketInfo.s) (quote goBracket) [ vArg s ]
  let t-under = op-under (quote BracketInfo.s) (quote goBracket) [ vArg t ]
  ans ← mirror-commands-alg rs s-under t-under
  normalise ans

mirror-commands-funseq rs s t = return (quoteTerm ℕ) -- TODO

mirror-commands-done rs s t = return (quoteTerm ℕ) -- TODO

macro
  mirror-test-helper : ∀ {i} {A : UU i} (f : A → A) {x : A} (a : Id (f (f x)) (f (f x))) (b : Id x x) → Term → TC ⊤
  mirror-test-helper f a b hole = do
    s ← quoteTC (□ ▸ a ▸ a ▷ f ⊚ f ⊚ ⟨| □ ▸ b ▸ b ▸ b |⟩ ▸ a ▸ a)
    t ← quoteTC (□ ▸ a ▸ a ▷ f ⊚ f ⊚ ⟨| □ ▸ b ▸ inv b ▸ b ▸ b ▸ b |⟩ ▸ a ▸ a)
    ans ← withNormalisation true (mirror-commands-alg (Select 2 ::R SegUnder 2 ::R UnderBracket ::R Zoom 1 0 ::R □R) s t)
    unify hole ans

mirror-test : ∀ {i} {A : UU i} (f : A → A) {x : A} (a : Id (f (f x)) (f (f x))) (b : Id x x) → _
mirror-test f a b = mirror-test-helper f a b

infix 11  _=∎
infixr 10 _=⟨↑_⟩_ _=⟨↓_⟩_ _=⟨↑_&_⟩_ _=⟨↓_&_⟩_

macro
  _=⟨↓_⟩_ : ∀ {i} {A : UU i} {x y : A} (s : PathAlg x y) (rs : ReasoningSeq ptAlg ptDone)
    {t w : PathAlg x y} (α : IdAlg t w) → Term → TC ⊤
  _=⟨↓_⟩_ {i} s rs {t = t} α goal =  withNormalisation true (do
    s' ← quoteTC s
    rs' ← quoteTC rs
    β ← unquoteTC {A = IdAlg s t}
      (def (quote reason-done)
        (vArg s'
        ∷ vArg rs'
        ∷ vArg (con (quote any-j) [ vArg unknown ]) ∷ []))
    ans ← withNormalisation false (quoteTC (β ·alg α))
    unify goal ans)
    
macro
  _=⟨↓_&_⟩_ : ∀ {i} {A : UU i} {x y : A} (s : PathAlg x y) {pt : PathType} (rs : ReasoningSeq ptAlg pt)
    (req : Term) {t w : PathAlg x y} (α : IdAlg t w) → Term → TC ⊤
  _=⟨↓_&_⟩_ s rs req {t = t} {w} α goal =  withNormalisation true (do
    s' ← quoteTC s
    t' ← quoteTC t
    target ← mirror-commands-alg rs s' t'
    full-req ← unquoteTC {A = reasoning-requierment s rs} (con (quote _,_) (vArg target ∷ vArg req ∷ []))
    β' ← quoteTC (reason-alg s rs full-req)
    β ←  unquoteTC {A = IdAlg s t} β'
    ans ←  withNormalisation false (quoteTC (β ·alg α))
    unify goal ans)

macro
  _=⟨↑_⟩_ : ∀ {i} {A : UU i} {x y : A} (s : PathAlg x y) (rs : ReasoningSeq ptAlg ptDone)
    {t w : PathAlg x y} (α : IdAlg t w) → Term → TC ⊤
  _=⟨↑_⟩_ s rs {t = t} {w} α goal = withNormalisation true (do
    t' ← quoteTC t
    rs' ← quoteTC rs
    β ← unquoteTC {A = IdAlg s t}
      (def (quote inv-alg)
        [ vArg (def (quote reason-done)
          (vArg t'
          ∷ vArg rs'
          ∷ vArg (con (quote any-j) [ vArg unknown ]) ∷ [])) ])
    ans ← withNormalisation false (quoteTC (β ·alg α))
    unify goal ans)

macro
  _=⟨↑_&_⟩_ : ∀ {i} {A : UU i} {x y : A} (s : PathAlg x y) {pt : PathType} (rs : ReasoningSeq ptAlg pt)
    (req : Term) {t w : PathAlg x y} (α : IdAlg t w) → Term → TC ⊤
  _=⟨↑_&_⟩_ s rs req {t = t} α goal =  withNormalisation true (do
    s' ← quoteTC s
    t' ← quoteTC t
    target ← mirror-commands-alg rs t' s'
    full-req ← unquoteTC {A = reasoning-requierment t rs} (con (quote _,_) (vArg target ∷ vArg req ∷ []))
    β' ←  (quoteTC (reason-alg t rs full-req))
    β ← unquoteTC {A = IdAlg t s} β'
    ans ←  withNormalisation false (quoteTC (inv-alg β ·alg α))
    unify goal ans)

_=∎ : ∀ {i} {A : UU i} {x y : A} (s : PathAlg x y) → IdAlg s s
s =∎ = refl-alg s
