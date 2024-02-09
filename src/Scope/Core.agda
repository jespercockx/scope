
module Scope.Core where

open import Haskell.Prelude hiding (All; _∘_)

open import Haskell.Law.Semigroup.Def using (IsLawfulSemigroup; associativity)
open import Haskell.Law.Semigroup.List using (iLawfulSemigroupList)
open import Haskell.Law.Monoid.Def
open import Haskell.Law.Monoid.List using (iLawfulMonoidList)
open import Haskell.Law.Equality
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
    -- we do this to get a transparent super field in the monoid instance
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

infixr 5 bind
syntax bind x α = x ◃ α

bindr : Scope name → name → Scope name
bindr α x = α <> [ x ]
{-# COMPILE AGDA2HS bindr #-}

infixr 5 bindr
syntax bindr α x = α ▹ x


opaque
  unfolding Scope

  caseScope : (α : Scope name) 
            → (@0 {{α ≡ mempty}} → c)
            → ((@0 x : name) (β : Scope name) → @0 {{α ≡ x ◃ β}} → c)
            → c
  caseScope [] emptyCase bindCase = emptyCase
  caseScope (Erased x ∷ β) emptyCase bindCase = bindCase x β

opaque
  unfolding Scope iLawfulSemigroupScope iLawfulMonoidScope

  rezzBind
    : {@0 α : Scope name} {@0 x : name}
    → Rezz _ α → Rezz _ (bind x α)
  rezzBind = rezzCong2 _∷_ rezzErase
  {-# COMPILE AGDA2HS rezzBind #-}

  rezzUnbind : {@0 x : name} {@0 α : Scope name} → Rezz _ (x ◃ α) → Rezz _ α
  rezzUnbind = rezzTail


opaque
  unfolding Scope iLawfulMonoidScope caseScope rezzBind
  ScopeCoreThings : Set₁
  ScopeCoreThings = Set
