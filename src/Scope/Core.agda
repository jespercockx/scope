module Scope.Core where

open import Haskell.Prelude hiding (All; _∘_)

open import Haskell.Law.Semigroup.Def using (IsLawfulSemigroup)
open import Haskell.Law.Semigroup.List using (iLawfulSemigroupList)
open import Haskell.Law.Monoid.Def using (IsLawfulMonoid)
open import Haskell.Law.Monoid.List using (iLawfulMonoidList)
open import Haskell.Extra.Erase
open import Haskell.Extra.Dec as Dec

open import Utils.Tactics
import Utils.List as List

private variable
  @0 name : Set

opaque
  Scope : (@0 name : Set) → Set
  Scope name = List (Erase name)
  {-# COMPILE AGDA2HS Scope #-}

  singleton : @0 name → Scope name
  singleton x = Erased x ∷ []
  {-# COMPILE AGDA2HS singleton #-}

  syntax singleton x = [ x ]

  instance
    iSemigroupScope : Semigroup (Scope name)
    iSemigroupScope = iSemigroupList

  private
    -- we do this to get a transparent super instance in the monoid instance
    scopeMempty : Scope name
    scopeMempty = mempty

    scopeMappend : Scope name → Scope name → Scope name
    scopeMappend = mappend

    scopeMConcat : List (Scope name) → Scope name
    scopeMConcat = mconcat

instance
  iMonoidScope : Monoid (Scope name)
  Monoid.super iMonoidScope = iSemigroupScope
  Monoid.mempty iMonoidScope = scopeMempty
  Monoid.mappend iMonoidScope = scopeMappend
  Monoid.mconcat iMonoidScope = scopeMConcat

opaque
  unfolding Scope
  instance
    iLawfulSemigroupScope : IsLawfulSemigroup (Scope name)
    iLawfulSemigroupScope = iLawfulSemigroupList

    iLawfulMonoidScope : IsLawfulMonoid (Scope name)
    iLawfulMonoidScope = iLawfulMonoidList

bind : @0 name → Scope name → Scope name
bind x α = singleton x <> α
{-# COMPILE AGDA2HS bind #-}

syntax bind x α = x ◃ α

opaque
  unfolding Scope

  rezzBind
    : {@0 α : Scope name} {@0 x : name}
    → Rezz _ α → Rezz _ (bind x α)
  rezzBind = rezzCong2 _∷_ rezzErase
  {-# COMPILE AGDA2HS rezzBind #-}
