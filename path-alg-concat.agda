{-# OPTIONS --without-K --exact-split  #-}

open import path-alg

module path-alg-concat {i} {A : UU i} where

infixl 29 _⋈_
_⋈_ : {x y z : A} → PathAlg x y → PathAlg y z → PathAlg x z
s ⋈ □ = s
s ⋈ t ▷ a = (s ⋈ t) ▷ a

⋈-lunit : {x y : A} (s : PathAlg x y) →
  Id (□ ⋈ s) s
⋈-lunit □ = refl □
⋈-lunit (s ▷ a) = ap (_▷ a) (⋈-lunit s)

-- This key lemma the performs rebracketing
↯-⋈ : {x y z : A} (s : PathAlg x y) (t : PathAlg y z) →
  IdAlg (s ⋈ t) (□ ▷ ⟨| s |⟩ ▷ ⟨| t |⟩)
↯-⋈ □ t = ⋈-lunit t *algL mk-id (inv (lrefl (↯ t)))
↯-⋈ s@(_ ▷ _) □ = mk-id (inv (rrefl (↯ s)))
↯-⋈ s@(_ ▷ _) (□ ▷ b) = mk-id (refl (↯ (s ▷ b)))
↯-⋈ s@(_ ▷ _)  (□ ▷ a ▷ b) = mk-id assoc
↯-⋈ s@(_ ▷ _)  (t@(_ ▷ _ ▷ _) ▷ a) = mk-id ((id↯ (↯-⋈ s t) ·R (↯-seg a)) · assoc)

infixr 29 _◁_
_◁_ : {x y z : A} → PathSeg x y → PathAlg y z → PathAlg x z
a ◁ s = □ ▷ a ⋈ s

⋈-assoc : {w x y z : A} (r : PathAlg w x) (s : PathAlg x y) (t : PathAlg y z) →
  Id (r ⋈ s ⋈ t) (r ⋈ (s ⋈ t))
⋈-assoc r s □ = refl (r ⋈ s)
⋈-assoc r s (t ▷ a) = ap (_▷ a) (⋈-assoc r s t)

-- Lemmas that compute instead of e.g. applying (λ u → (u ⋈ t))
_⋈R_ : {x y z : A} {s t : PathAlg x y} (p : IdAlg s t) (r : PathAlg y z) → IdAlg (s ⋈ r) (t ⋈ r)
p ⋈R □ = p
p ⋈R (r ▷ a) = (p ⋈R r) ▷R a

_◁R_ : {x y z : A} (a : PathSeg x y) {r s : PathAlg y z} (p : IdAlg r s) → IdAlg (a ◁ r) (a ◁ s)
_◁R_ a {r = r} {s = s} p = ↯-⋈ (□ ▷ a) r ·alg mk-id (↯-seg a ·L id↯ p) ·alg inv-alg (↯-⋈ (□ ▷ a) s)

_⋈L_ : {x y z : A} (s : PathAlg x y) {t r : PathAlg y z} (p : IdAlg t r) → IdAlg (s ⋈ t) (s ⋈ r)
_⋈L_ □ {t = t} {r = r} p = ⋈-lunit t *algL p *algR inv (⋈-lunit r)
_⋈L_ (s ▷ a) {t = t} {r = r} p =
  ⋈-assoc s (□ ▷ a) t *algL ↯-⋈ s (a ◁ t) ·alg mk-id (↯ s ·L (id↯ (a ◁R p))) ·alg inv-alg (↯-⋈ s (a ◁ r)) *algR  inv (⋈-assoc s (□ ▷ a) r)


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

record ZoomInfo {x y : A} (s : PathAlg x y) : UU (lsuc i) where
  constructor mk-ZoomInfo
  field
    {x' y'} : A
    init : PathAlg x x'
    middle : PathAlg x' y'
    final : PathAlg y' y
    p : Id s (init ⋈ (middle ⋈ final))

private
  z-x = ZoomInfo.x'
  z-y = ZoomInfo.y'
  z-init = ZoomInfo.init
  z-middle = ZoomInfo.middle
  z-final = ZoomInfo.final

goZoom : {x y : A} (s : PathAlg x y) (n m : ℕ) → ZoomInfo s
goZoom s n m =
  mk-ZoomInfo
    (take n s) (take m (drop n s)) (drop m (drop n s))
    (inv (take-drop-unsplit n s) · ap (take n s ⋈_) (inv (take-drop-unsplit m (drop n s))))

replaceZoom : {x y : A} {s : PathAlg x y} (info : ZoomInfo s) {t : PathAlg (z-x info) (z-y info)} →
  IdAlg (z-middle info) t → IdAlg s (z-init info ⋈ (t ⋈ z-final info))
replaceZoom (mk-ZoomInfo init middle final p) {t = t} q = p *algL (init ⋈L (q ⋈R final))

lrefl-id : {x y : A} (a : Id x y) → IdAlg (□ ▷ △ a) (□ ▷ △ (refl x) ▷ △ a)
lrefl-id a = mk-id (inv (lrefl a))

make5 : {x : A} (a : Id x x) → PathAlg x x
make5 a = □ ▷ △ a  ▷ △ a  ▷ △ a  ▷ △ a  ▷ △ a

lem : {x : A} (a : Id x x) → UU i
lem a = {!replaceZoom (goZoom (make5 a) 2 1) (lrefl-id a)!}
