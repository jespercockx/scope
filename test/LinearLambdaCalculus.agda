

module LinearLambdaCalculus where

open import Haskell.Prelude
open import Scope

postulate
  name : Set

variable
  @0 α α₁ α₂ : Scope name

data Term (@0 α : Scope name) : Set where
  Var : (@0 x : name) → @0 (α ≡ [ x ]) → Term α
  Lam : (@0 y : name) → Term (y ◃ α) → Term α
  App : α₁ ⋈ α₂ ≡ α → Term α₁ → Term α₂ → Term α
{-# COMPILE AGDA2HS Term deriving Show #-}

postulate
  i j k : name

var! : (@0 x : name) → Term [ x ]
var! x = Var x refl
{-# INLINE var! #-}

opaque
  unfolding singleton

  myterm : Term mempty
  myterm = Lam i (Lam j (App (splitBindRight splitEmptyRight) (var! i) (var! j)))

  {-# COMPILE AGDA2HS myterm #-}