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

  --TODO: fix proofs, take a look at @Jesper's lecture notes, there should be an elegant proof that goes through the naïve version of revScope
  revScopeMempty : revScope {name = name} mempty ≡ mempty
  revScopeMempty = refl

  revScopeAccCom : (s p : Scope name) → revScopeAcc s p ≡ revScope s <> p
  revScopeAccCom [] p = refl
  revScopeAccCom (x ∷ s) p
    rewrite (revScopeAccCom s (x ∷ p))
    rewrite (revScopeAccCom s (x ∷ []))
    = associativity (revScopeAcc s []) (x ∷ []) p

  revMappendDist : (s p : Scope name) → revScope (s <> p) ≡ (revScope p) <> (revScope s)
  revMappendDist [] p = sym (rightIdentity (revScope p))
  revMappendDist (x ∷ s) p = {!revMappendDist s (x ∷ p)!}

  revrevid : (s : Scope name) → revScope (revScope s) ≡ s
  revrevid [] = refl
  revrevid (x ∷ s) = begin
    revScope (revScope (x ∷ s))
    ≡⟨ cong revScope (revScopeAccCom s (x ∷ [])) ⟩
    revScope (revScope s <> (x ∷ []))
    ≡⟨ revScopeAccCom {!revScope s!} {!!} ⟩
    {!!}
    ≡⟨ {!!} ⟩
    {!!}
    ∎

  --revBind : (s : Scope name) → (@0 x : name) → revScope (x ◃ s) ≡ (revScope s) ▹ x
  --revBind [] x = refl
  --revBind (Erased y ∷ s) x = cong (λ p → p <> [ x ]) (revBind s y)
