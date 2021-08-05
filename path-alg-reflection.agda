{-# OPTIONS --without-K --exact-split  #-}

module path-alg-reflection where

open import path-alg-reasoning
open import Reflection
open import Reflection.Term
open import Reflection.Pattern
open import Data.String as String
open import Data.List as List

infix 11  _=∎
infixr 10 _=⟨↑_⟩_ _=⟨↓_⟩_ _=⟨↑_&_⟩_ _=⟨↓_&_⟩_

macro
  _=⟨↓_⟩_ : ∀ {i} {A : UU i} {x y : A} (s : PathAlg x y) (rs : ReasoningSeq ptAlg ptDone)
    {t w : PathAlg x y} (α : IdAlg t w) → Term → TC ⊤
  _=⟨↓_⟩_ s rs {w = w} α goal = do
    τ ← quoteTC (IdAlg s w)
    s' ← quoteTC s
    rs' ← quoteTC rs
    α' ← quoteTC α
    unify goal
       (def (quote _·alg_)
         (vArg (def (quote reason-done)
           (vArg s'
           ∷ vArg rs'
           ∷ vArg (con (quote any-j) [ vArg unknown ]) ∷ []))
         ∷ vArg α' ∷ []))

macro
  _=⟨↓_&_⟩_ : ∀ {i} {A : UU i} {x y : A} (s : PathAlg x y)  {pt : PathType} (rs : ReasoningSeq ptAlg pt)
    (req : reasoning-requierment s rs) {t w : PathAlg x y} (α : IdAlg t w) → Term → TC ⊤
  _=⟨↓_&_⟩_ s rs req {w = w} α goal = do
    τ ← quoteTC (IdAlg s w)
    β ← quoteTC (reason-alg s rs req)
    α' ← quoteTC α
    unify goal (def (quote _·alg_) (vArg β ∷ vArg α' ∷ []))

macro
  _=⟨↑_⟩_ : ∀ {i} {A : UU i} {x y : A} (s : PathAlg x y) (rs : ReasoningSeq ptAlg ptDone)
    {t w : PathAlg x y} (α : IdAlg t w) → Term → TC ⊤
  _=⟨↑_⟩_ s rs {t = t} {w} α goal = do
    τ ← quoteTC (IdAlg s w)
    t' ← quoteTC t
    rs' ← quoteTC rs
    α' ← quoteTC α
    unify goal
      (def (quote _·alg_)
        (vArg (def (quote inv-alg)
          [ vArg (def (quote reason-done)
            (vArg t'
            ∷ vArg rs'
            ∷ vArg (con (quote any-j) [ vArg unknown ]) ∷ [])) ])
      ∷ vArg α' ∷ []))

macro
  _=⟨↑_&_⟩_ : ∀ {i} {A : UU i} {x y : A} (s : PathAlg x y) {pt : PathType} (rs : ReasoningSeq ptAlg pt)
    {t w : PathAlg x y} (req : reasoning-requierment t rs) (α : IdAlg t w) → Term → TC ⊤
  _=⟨↑_&_⟩_ s rs {t = t} {w} req α goal = do
    τ ← quoteTC (IdAlg s w)
    β ← quoteTC (reason-alg t rs req)
    α' ← quoteTC α
    unify goal (def (quote _·alg_) (vArg (def (quote inv-alg) [ vArg β ]) ∷ vArg α' ∷ []))

_=∎ : ∀ {i} {A : UU i} {x y : A} (s : PathAlg x y) → IdAlg s s
s =∎ = refl-alg s

macro-test1 : ∀ {i} {A : UU i} (f : A → A) {x : A} (a : Id (f (f x)) (f (f x))) (b : Id x x) →
  Id (a · a · ap f (ap f (b · b · b)) · a · a) (a · a · ap (f ∘ f) (b · inv b · b · b · b) · a · a)
macro-test1 f a b = id↯
  (□ ▸ a ▸ a ▷ f ⊚ f ⊚ ⟨| □ ▸ b ▸ b ▸ b |⟩ ▸ a ▸ a
    =⟨↓ (Select 2 ::R SegUnder 2 ::R UnderBracket ::R Zoom 1 0 ::R □R) & □ ▸ inv b ▸ b , inv (linv b) ⟩
   □ ▸ a ▸ a ▷ f ⊚ f ⊚ ⟨| □ ▸ b ▸ inv b ▸ b ▸ b ▸ b |⟩ ▸ a ▸ a
    =⟨↓ Select 2 ::R FunsOver 2 ::R CollapseFuns ::R □R ⟩
   □ ▸ a ▸ a ▷ (f ∘ f) ⊚ ⟨| □ ▸ b ▸ inv b ▸ b ▸ b ▸ b |⟩ ▸ a ▸ a
    =∎)

macro-test2 : ∀ {i} {A : UU i} (f : A → A) {x : A} (a : Id (f (f x)) (f (f x))) (b : Id x x) →
  Id (a · a · ap (f ∘ f) (b · b · b) · a · a) (a · a · ap f (ap f (b · inv b · b · b · b)) · a · a)
macro-test2 f a b = id↯
  ((□ ▸ a ▸ a ▷ (f ∘ f) ⊚ ⟨| □ ▸ b ▸ b ▸ b |⟩ ▸ a ▸ a
    =⟨↑ (Select 2 ::R SegUnder 1 ::R UnderBracket ::R Zoom 0 2 ::R □R) & □ , rinv b ⟩
   □ ▸ a ▸ a ▷ (f ∘ f) ⊚ ⟨| □ ▸ b ▸ inv b ▸ b ▸ b ▸ b |⟩ ▸ a ▸ a
    =⟨↑ Select 2 ::R FunsOver 2 ::R CollapseFuns ::R □R ⟩
   □ ▸ a ▸ a ▷ f ⊚ f ⊚ ⟨| □ ▸ b ▸ inv b ▸ b ▸ b ▸ b |⟩ ▸ a ▸ a
    =∎))