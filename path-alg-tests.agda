{-# OPTIONS --without-K --exact-split #-}

module path-alg-tests where

open import path-alg-reasoning
open import path-alg-reflection

macro-test1 : ∀ {i} {A : UU i} (f : A → A) {x : A} (a : Id (f (f x)) (f (f x))) (b : Id x x) → _
--  Id (a · a · ap f (ap f (b · b · b)) · a · a) (a · a · ap (f ∘ f) (b · inv b · b · b · b) · a · a)
macro-test1 f a b = --id↯
  (□ ▸ a ▸ a ▷ f ⊚ f ⊚ ⟨| □ ▸ b ▸ b ▸ b |⟩ ▸ a ▸ a
    =⟨↓ Select 2 ::R SegUnder 2 ::R UnderBracket ::R Zoom 0 0 ::R □R & inv (rinv b) ⟩
   □ ▸ a ▸ a ▷ f ⊚ f ⊚ ⟨| □ ▸ b ▸ inv b ▸ b ▸ b ▸ b |⟩ ▸ a ▸ a
    =⟨↓ Select 2 ::R FunsOver 2 ::R CollapseFuns ::R □R ⟩
   □ ▸ a ▸ a ▷ (f ∘ f) ⊚ ⟨| □ ▸ b ▸ inv b ▸ b ▸ b ▸ b |⟩ ▸ a ▸ a
    =∎)

{-macro-test2 : ∀ {i} {A : UU i} (f : A → A) {x : A} (a : Id (f (f x)) (f (f x))) (b : Id x x) →
  Id (a · a · ap (f ∘ f) (b · b · b) · a · a) (a · a · ap f (ap f (b · inv b · b · b · b)) · a · a)
macro-test2 f a b = id↯
  (□ ▸ a ▸ a ▷ (f ∘ f) ⊚ ⟨| □ ▸ b ▸ b ▸ b |⟩ ▸ a ▸ a
    =⟨↑ Select 2 ::R SegUnder 1 ::R UnderBracket ::R Zoom 0 2 ::R □R & rinv b ⟩
   □ ▸ a ▸ a ▷ (f ∘ f) ⊚ ⟨| □ ▸ b ▸ inv b ▸ b ▸ b ▸ b |⟩ ▸ a ▸ a
    =⟨↑ Select 2 ::R FunsOver 2 ::R CollapseFuns ::R □R ⟩
   □ ▸ a ▸ a ▷ f ⊚ f ⊚ ⟨| □ ▸ b ▸ inv b ▸ b ▸ b ▸ b |⟩ ▸ a ▸ a
    =∎)-}
