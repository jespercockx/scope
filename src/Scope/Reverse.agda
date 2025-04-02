
module Scope.Reverse where

open import Haskell.Prelude hiding (All; _∘_)

open import Haskell.Law.Semigroup.Def using (IsLawfulSemigroup; associativity)
open import Haskell.Law.Semigroup.List using (iLawfulSemigroupList)
open import Haskell.Law.Monoid.Def
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
  revScope s = revScopeAcc s []
  {-# COMPILE AGDA2HS revScope #-}

infix 7 revScope
syntax revScope r = ~ r

opaque
  unfolding revScope

  revScopeAccComp : (s p : Scope name) → revScopeAcc s p ≡ p <> ~ s
  revScopeAccComp [] p = refl
  revScopeAccComp (x ∷ s) p
    rewrite (revScopeAccComp s (x ∷ p))
    rewrite (revScopeAccComp s (x ∷ []))
    = associativity ⦃ iSemigroupA = iSemigroupList ⦄ (revScopeAcc s []) (x ∷ []) p

  private
    rev' : Scope name → Scope name
    rev' [] = []
    rev' (Erased x ∷ s) = rev' s ++ [ x ]

    revsrev' : (s : Scope name) → revScope s ≡ rev' s
    revsrev' [] = refl
    revsrev' (x ∷ s)
      rewrite (revScopeAccComp s (x ∷ []))
      = cong (λ t → t ++ (x ∷ [])) (revsrev' s)

    rev'Dist : (s p : Scope name) → rev' (p <> s) ≡ (rev' s) <> (rev' p)
    rev'Dist [] p = sym (leftIdentity ⦃ iMonoidA = iMonoidScope ⦄ (rev' p))
    rev'Dist (x ∷ s) p =
      begin
      rev' (s ++ p) ++ (x ∷ [])
      ≡⟨ cong (λ a → a ++ (x ∷ [])) (rev'Dist s p) ⟩
      (rev' p ++ rev' s) ++ (x ∷ [])
      ≡⟨ sym (associativity ⦃ iSemigroupA = iSemigroupList ⦄ (rev' p) (rev' s) (x ∷ [])) ⟩
      (rev' p) ++ (rev' (x ∷ s))
      ∎

    rev'Involution : (s : Scope name) → rev' (rev' s) ≡ s
    rev'Involution [] = refl
    rev'Involution (x ∷ s)
      = trans (rev'Dist (rev' s) (x ∷ [])) (cong (λ a → x ∷ a) (rev'Involution s))

  revsIdentity : revScope {name = name} mempty ≡ mempty
  revsIdentity = refl

  revsDist : (s p : Scope name) → ~ (s <> p) ≡ ~ p <> ~ s
  revsDist s p
    rewrite revsrev' s
    rewrite revsrev' p
    = trans (revsrev' (p ++ s)) (rev'Dist p s)

  revsInvolution : (s : Scope name) → ~ ~ s ≡ s
  revsInvolution s
    rewrite revsrev' s
    rewrite revsrev' (rev' s)
    = rev'Involution s

opaque
  unfolding revScope revScopeAccComp

  ReverseThings : Set₁
  ReverseThings = Set
