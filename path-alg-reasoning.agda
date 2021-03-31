{-# OPTIONS --without-K --exact-split  #-}

module path-alg-reasoning where

open import path-alg
open import path-alg-concat
open import path-alg-ap
open import Data.Maybe as Maybe using (Maybe; just; nothing; maybe)

module _ {i} where
  record UnderInfo {B : UU i} {x' y' : B} (b : PathSeg x' y') : UU (lsuc i) where
    constructor mk-UnderInfo
    field
      {A} : UU i
      f : A → B
      {x y} : A
      a : PathSeg x y
      px : Id (f x) x'
      py : Id (f y) y'

  goUnder : {A : UU i} {x y : A} (a : PathSeg x y) → Maybe (UnderInfo a)
  goUnder (△ x) = nothing
  goUnder ⟨| x |⟩ = nothing
  goUnder (p-inv a) = nothing
  goUnder (f ⊚ a) = just (mk-UnderInfo f a (refl _) (refl _))

