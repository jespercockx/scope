
module Scope.Reverse where

open import Haskell.Prelude hiding (All; _∘_)

open import Haskell.Law.Semigroup.Def using (IsLawfulSemigroup; associativity)
open import Haskell.Law.Semigroup.List using (iLawfulSemigroupList)
open import Haskell.Law.Monoid.Def
open import Haskell.Law.Monoid.List using (iLawfulMonoidList)
open import Haskell.Law.Equality
open import Haskell.Extra.Erase
open import Haskell.Extra.Dec as Dec

open import Scope.Core

private variable
  @0 name : Set

opaque
  unfolding Scope

  revScopeAcc : Scope name → Scope name → Scope name
  revScopeAcc [] acc = acc
  revScopeAcc (x ∷ s) acc = revScopeAcc s (x ∷ acc)
  {-# COMPILE AGDA2HS revScopeAcc #-}

  revScope : Scope name → Scope name
  revScope = flip revScopeAcc []
  {-# COMPILE AGDA2HS revScope #-}
  
infix 7 revScope
syntax revScope r = ~ r

opaque
  unfolding revScope iLawfulMonoidScope

  revScopeAccComp : (s p : Scope name) → revScopeAcc s p ≡ ~ s <> p
  revScopeAccComp [] p = refl
  revScopeAccComp (x ∷ s) p
    rewrite (revScopeAccComp s (x ∷ p))
    rewrite (revScopeAccComp s (x ∷ []))
    = associativity (revScopeAcc s []) (x ∷ []) p

  private
    rev' : Scope name → Scope name
    rev' [] = []
    rev' (x ∷ s) = rev' s <> (x ∷ [])

    revsrev' : (s : Scope name) → revScope s ≡ rev' s
    revsrev' [] = refl
    revsrev' (x ∷ s)
      rewrite (revScopeAccComp s (x ∷ []))
      = cong (λ t → t <> (x ∷ [])) (revsrev' s)

    rev'Dist : (s p : Scope name) → rev' (s <> p) ≡ (rev' p) <> (rev' s)
    rev'Dist [] p = sym (rightIdentity (rev' p))
    rev'Dist (x ∷ s) p = begin
      rev' ((x ∷ s) <> p)
      ≡⟨ cong (λ s → s <> (x ∷ [])) (rev'Dist s p) ⟩
      (rev' p <> rev' s) <> (x ∷ [])
      ≡⟨ sym (associativity (rev' p) (rev' s) (x ∷ [])) ⟩
      (rev' p) <> (rev' (x ∷ s))
      ∎

    rev'Involution : (s : Scope name) → rev' (rev' s) ≡ s
    rev'Involution [] = refl
    rev'Involution (x ∷ s)
      rewrite rev'Dist (rev' s) (x ∷ [])
      rewrite rev'Involution s
      = refl

    rev'BindComp : (s : Scope name) → (@0 x : name) → rev' (x ◃ s) ≡ (rev' s) ▹ x
    rev'BindComp s x = refl

  revsIdentity : revScope {name = name} mempty ≡ mempty
  revsIdentity = refl

  revsDist : (s p : Scope name) → ~ (s <> p) ≡ ~ p <> ~ s
  revsDist s p
    rewrite revsrev' s
    rewrite revsrev' p
    rewrite revsrev' (s <> p)
    = rev'Dist s p

  revsInvolution : (s : Scope name) → ~ ~ s ≡ s
  revsInvolution s
    rewrite revsrev' s
    rewrite revsrev' (rev' s)
    = rev'Involution s

  revsBindComp : (s : Scope name) → (@0 x : name) → ~ (x ◃ s) ≡ ~ s ▹ x
  revsBindComp s x
    rewrite revsrev' (x ◃ s)
    rewrite revsrev' s
    = rev'BindComp s x

opaque
  unfolding revScope revScopeAccComp

  ReverseThings : Set₁
  ReverseThings = Set
