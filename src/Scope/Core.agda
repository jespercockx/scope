{-# OPTIONS --allow-unsolved-metas #-}
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

  revScopeAcc : Scope name → Scope name → Scope name
  revScopeAcc [] acc = acc
  revScopeAcc (x ∷ s) acc = revScopeAcc s (x ∷ acc)

  --TODO: find nicer syntax
  revScope : Scope name → Scope name
  revScope = flip revScopeAcc []

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

bindr : Scope name → name → Scope name
bindr α x = α <> [ x ]
{-# COMPILE AGDA2HS bindr #-}

syntax bindr α x = α ▹ x

opaque
  unfolding Scope

  rezzBind
    : {@0 α : Scope name} {@0 x : name}
    → Rezz _ α → Rezz _ (bind x α)
  rezzBind = rezzCong2 _∷_ rezzErase
  {-# COMPILE AGDA2HS rezzBind #-}

  revScopeAccComp : (s p : Scope name) → revScopeAcc s p ≡ revScope s <> p
  revScopeAccComp [] p = refl
  revScopeAccComp (x ∷ s) p
    rewrite (revScopeAccComp s (x ∷ p))
    rewrite (revScopeAccComp s (x ∷ []))
    = associativity ⦃ _ ⦄ ⦃ iLawfulSemigroupScope ⦄ (revScopeAcc s []) (x ∷ []) p

  private
    rev' : Scope name → Scope name
    rev' [] = []
    rev' (x ∷ s) = rev' s <> (x ∷ [])

    revsrev' : (s : Scope name) → revScope s ≡ rev' s
    revsrev' [] = refl
    revsrev' (x ∷ s)
      rewrite (revScopeAccComp s (x ∷ []))
      = cong (λ t → t <> (x ∷ [])) (revsrev' s)

    rev'md : (s p : Scope name) → rev' (s <> p) ≡ (rev' p) <> (rev' s)
    rev'md [] p = sym (rightIdentity ⦃ _ ⦄ ⦃ iLawfulMonoidScope ⦄ (rev' p))
    rev'md (x ∷ s) p = begin
      rev' ((x ∷ s) <> p)
      ≡⟨ cong (λ s → s <> (x ∷ [])) (rev'md s p) ⟩
      (rev' p <> rev' s) <> (x ∷ [])
      ≡⟨ sym (associativity ⦃ _ ⦄ ⦃ iLawfulSemigroupList ⦄ (rev' p) (rev' s) (x ∷ [])) ⟩
      (rev' p) <> (rev' (x ∷ s))
      ∎

    rev'rev'id : (s : Scope name) → rev' (rev' s) ≡ s
    rev'rev'id [] = refl
    rev'rev'id (x ∷ s)
      rewrite rev'md (rev' s) (x ∷ [])
      rewrite rev'rev'id s
      = refl

    rev'bind : (s : Scope name) → (@0 x : name) → rev' (x ◃ s) ≡ (rev' s) ▹ x
    rev'bind s x = refl

  revScopeMempty : revScope {name = name} mempty ≡ mempty
  revScopeMempty = refl

  revsMappendDist : (s p : Scope name)
                      → revScope (s <> p) ≡ (revScope p) <> (revScope s)
  revsMappendDist s p
    rewrite revsrev' s
    rewrite revsrev' p
    rewrite revsrev' (s <> p)
    = rev'md s p

  revsRevsId : (s : Scope name) → revScope (revScope s) ≡ s
  revsRevsId s
    rewrite revsrev' s
    rewrite revsrev' (rev' s)
    = rev'rev'id s

  revsBind : (s : Scope name) → (@0 x : name) → revScope (x ◃ s) ≡ (revScope s) ▹ x
  revsBind s x
    rewrite revsrev' (x ◃ s)
    rewrite revsrev' s
    = rev'bind s x
