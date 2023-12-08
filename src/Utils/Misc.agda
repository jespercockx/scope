module Utils.Misc where

open import Agda.Builtin.Equality

subst
  : ∀ {ℓ ℓ′} {@0 a : Set ℓ}
    (@0 f : @0 a → Set ℓ′)
    {@0 x y : a}
  → @0 x ≡ y → f x → f y
subst f refl x = x
{-# COMPILE AGDA2HS subst transparent #-}
