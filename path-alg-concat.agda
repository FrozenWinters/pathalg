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

_◁R_ : {x y z : A} {a b : PathSeg x y} (p : IdSeg a b) (s : PathAlg y z) → IdAlg (a ◁ s) (b ◁ s)
p ◁R □ = mk-id (id-seg↯ p)
p ◁R (s ▷ a) = (p ◁R s) ▷R a

_◁L_ : {x y z : A} (a : PathSeg x y) {r s : PathAlg y z} (p : IdAlg r s) → IdAlg (a ◁ r) (a ◁ s)
_◁L_ a {r = r} {s = s} p = ↯-⋈ (□ ▷ a) r ·alg mk-id (↯-seg a ·L id↯ p) ·alg inv-alg (↯-⋈ (□ ▷ a) s)

_⋈L_ : {x y z : A} (s : PathAlg x y) {t r : PathAlg y z} (p : IdAlg t r) → IdAlg (s ⋈ t) (s ⋈ r)
_⋈L_ □ {t = t} {r = r} p = ⋈-lunit t *algL p *algR inv (⋈-lunit r)
_⋈L_ (s ▷ a) {t = t} {r = r} p =
  ⋈-assoc s (□ ▷ a) t *algL ↯-⋈ s (a ◁ t) ·alg mk-id (↯ s ·L (id↯ (a ◁L p))) ·alg inv-alg (↯-⋈ s (a ◁ r)) *algR  inv (⋈-assoc s (□ ▷ a) r)

module PathAlgOps where
  Is-nonempty : {x y : A} → PathAlg x y → (UU lzero)
  Is-nonempty □ = ⊥
  Is-nonempty (s ▷ a) = ⊤

  nonempty? : {x y : A} → (s : PathAlg x y) → (Is-nonempty s) + ⊤
  nonempty? □ = inr unit
  nonempty? (s ▷ a) = inl unit

  split : {x y : A} → PathAlg x y → Σ A (λ z → (PathSeg x z) × (PathAlg z y))
  split {x = x} □ = (x , (△ refl x , □))
  split {y = y} (□ ▷ a) = (y , (a , □))
  split (s@(_ ▷ _) ▷ a) =
    let (z , (c , t)) = split s
    in (z , (c , t ▷ a))

  unsplit-type : {x y : A} → PathAlg x y → UU (lsuc i)
  unsplit-type s =
    let  (_ , (b , t)) = split s
    in Id (□ ▷ b ⋈ t) s

  unsplit : {x y : A} → (s : PathAlg x y) → Is-nonempty s → unsplit-type s
  unsplit (□ ▷ a) _ = refl (□ ▷ a)
  unsplit (s@(_ ▷ _) ▷ a) _ =
    let  (z , (c , t)) = split s
    in  ap (_▷ a) (unsplit s unit)

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
       · (unsplit s unit)

  first : {x y : A} (s : PathAlg x y) → Is-nonempty s → (PathSeg x (point-from-start 1 s))
  first s@(_ ▷ _) _ = pr₁ (pr₂ (split s))

  first-rest-unsplit : {x y : A} → (s : PathAlg x y) → (p : Is-nonempty s) → Id ((first s p) ◁ (drop 1 s)) s
  first-rest-unsplit s@(_ ▷ _) p = unsplit s p

  length : {x y : A} (s : PathAlg x y) → ℕ
  length □ = 0
  length (s ▷ a) = S (length s)

  point-from-end : (n : ℕ) {x y : A} → PathAlg x y → A
  point-from-end Z {y = y} s = y
  point-from-end (S k) {x = x} □ = x
  point-from-end (S k) (s ▷ x) = point-from-end k s

  drop-from-end : (n : ℕ) {x y : A} (s : PathAlg x y) →
    PathAlg x (point-from-end n s)
  drop-from-end Z s = s
  drop-from-end (S k) □ = □
  drop-from-end (S k) (s ▷ x) = drop-from-end k s

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

record SelectInfo {x y : A} (s : PathAlg x y) : UU (lsuc i) where
  constructor mk-SelectInfo
  field
    {x' y'} : A
    init : PathAlg x x'
    middle : PathSeg x' y'
    final : PathAlg y' y
    p : Id s (init ⋈ (middle ◁ final))

private
  s-x = SelectInfo.x'
  s-y = SelectInfo.y'
  s-init = SelectInfo.init
  s-middle = SelectInfo.middle
  s-final = SelectInfo.final

open PathAlgOps

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

zoom-test : {x : A} (a : Id x x) →
  Id (a · a · a · a · a) (a · a · refl x · a · a · a)
zoom-test a = id↯ (replaceZoom (goZoom (make5 a) 2 1) (lrefl-id a))

goSelect-helper : {x y : A} (s : PathAlg x y) (n : ℕ) → Is-nonempty (drop n s) → SelectInfo s
goSelect-helper s n p = mk-SelectInfo (take n s) (first (drop n s) p) ((drop 1 (drop n s)))
                                      (inv (take-drop-unsplit n s) ·  ap (take n s ⋈_) (inv (first-rest-unsplit (drop n s) p)))

goSelect : {x y : A} (s : PathAlg x y) (n : ℕ) → Maybe (SelectInfo s)
goSelect s n with nonempty? (drop n s)
... | inl p = just (goSelect-helper s n p)
... | inr _ = nothing

replaceSelect : {x y : A} {s : PathAlg x y} (info : SelectInfo s) {b : PathSeg (s-x info) (s-y info)} →
  IdSeg (s-middle info) b → IdAlg s (s-init info ⋈ (b ◁ s-final info))
replaceSelect (mk-SelectInfo init middle final p) {b = b} q = p *algL (init ⋈L (q ◁R final))

lrefl-id-seg' : {A : UU i} {x y : A} (a : Id x y) → IdSeg (△ a) ⟨| □ ▷ △ (refl x) ▷ △ a |⟩
lrefl-id-seg' a = mk-seg-id (inv (lrefl a))

select-test : {x : A} (a : Id x x) →
  IdAlg (□ ▷ △ a ▷ △ a ▷ △ a ▷ △ a ▷ △ a) (□ ▷ △ a ▷ △ a ▷ ⟨| □ ▷ △ refl x ▷ △ a |⟩ ▷ △ a ▷ △ a)
select-test a = replaceSelect (to-witness-T (goSelect (make5 a) 2) _) (lrefl-id-seg' a)
