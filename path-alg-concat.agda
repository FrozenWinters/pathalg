{-# OPTIONS --without-K --exact-split  #-}

open import path-alg

module path-alg-concat {i} {A : UU i} where

infixl 29 _⋈_
_⋈_ : {x y z : A} → PathAlg x y → PathAlg y z → PathAlg x z
s ⋈ □ = s
s ⋈ t ▷ a = (s ⋈ t) ▷ a

-- This key lemma the performs rebracketing
↯-⋈ : {x y z : A} (s : PathAlg x y) (t : PathAlg y z) →
  IdAlg (s ⋈ t) (□ ▷ ⟨| s |⟩ ▷ ⟨| t |⟩)
↯-⋈ s □ = mk-id (inv (rrefl (↯ s)))
↯-⋈ s (t@(_ ▷ _) ▷ a) = mk-id ((id↯ (↯-⋈ s t) ·R ↯-seg a) · assoc)
↯-⋈ □ (□ ▷ a) = mk-id (inv (lrefl (↯-seg a)))
↯-⋈ s@(_ ▷ _) (□ ▷ b) = mk-id (refl (↯ s · ↯-seg b))

infixr 29 _◁_
_◁_ : {x y z : A} → PathSeg x y → PathAlg y z → PathAlg x z
a ◁ s = □ ▷ a ⋈ s

⋈-lunit : {x y : A} (s : PathAlg x y) →
  Id (□ ⋈ s) s
⋈-lunit □ = refl □
⋈-lunit (s ▷ a) = ap (_▷ a) (⋈-lunit s)

⋈-assoc : {w x y z : A} (r : PathAlg w x) (s : PathAlg x y) (t : PathAlg y z) →
  Id (r ⋈ s ⋈ t) (r ⋈ (s ⋈ t))
⋈-assoc r s □ = refl (r ⋈ s)
⋈-assoc r s (t ▷ a) = ap (_▷ a) (⋈-assoc r s t)

private
  split : {x y : A} → PathAlg x y → Σ A (λ z → (PathSeg x z) × (PathAlg z y))
  split {x = x} □ = (x , (△ refl x , □))
  split {y = y} (□ ▷ a) = (y , (a , □))
  split (s@(_ ▷ _) ▷ a) =
    let (z , (c , t)) = split s
    in (z , (c , t ▷ a))

  unsplit-type : {x y : A} → PathAlg x y → UU (lsuc i)
  unsplit-type {x = x} □ = Lift ⊤
  unsplit-type s@(_ ▷ _) =
    let  (_ , (b , t)) = split s
    in Id (□ ▷ b ⋈ t) s

  unsplit : {x y : A} → (s : PathAlg x y) → unsplit-type s
  unsplit □ = lift unit
  unsplit (□  ▷ a) = refl (□ ▷ a)
  unsplit (s@(_ ▷ _) ▷ a) =
    let  (z , (c , t)) = split s
    in  ap (_▷ a) (unsplit s)

  point-from-start : (n : ℕ) {x y : A} → PathAlg x y → A
  point-from-start Z {x = x} s = x
  point-from-start (S n) {y = y} □ = y
  point-from-start (S n) s@(_ ▷ _) =
    let (_ , (_ , t)) = split s
    in point-from-start n t

  take : (n : ℕ) {x y : A} (s : PathAlg x y) →
    PathAlg x (point-from-start n s)
  take Z s = □
  take (S n) □ = □
  take (S n) s@(_ ▷ _) =
    let (_ , (b , t)) = split s
    in b ◁ take n t

  drop : (n : ℕ) {x y : A} (s : PathAlg x y) →
    PathAlg (point-from-start n s) y
  drop Z s = s
  drop (S n) □ = □
  drop (S n) s@(_ ▷ _) =
    let (_ , (_ , t)) = split s
    in drop n t

  take-drop-unsplit : (n : ℕ) {x y : A} (s : PathAlg x y) →
    Id (take n s ⋈ drop n s) s
  take-drop-unsplit Z s = ⋈-lunit s
  take-drop-unsplit (S n) □ = refl □
  take-drop-unsplit (S n) s@(_ ▷ _) =
    let (_ , (b , t)) = split s
    in ⋈-assoc (□ ▷ b) (take n t) (drop n t)
       · ap (b ◁_) (take-drop-unsplit n t)
       · unsplit s


