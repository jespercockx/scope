open import Haskell.Prelude hiding (coerce)
open import Haskell.Extra.Refinement
open import Haskell.Extra.Erase
open import Haskell.Law.Equality

open import Scope.Core
open import Scope.Split
open import Scope.Sub
open import Scope.In

module Scope.Cut where

private variable
  @0 name : Set
  @0 x : name
  @0 α α' : Scope name

opaque
  unfolding Scope
  @0 cut : {α : Scope name} → x ∈ α → Scope name × Scope name
  cut {α = _ ∷ α'} (Zero  ⟨ p ⟩) = α' , mempty
  cut {α = iErased ∷ α} (Suc n ⟨ IsSuc p ⟩) = do
    let α₀ , α₁ = cut (n ⟨ p ⟩)
    α₀ , iErased ∷ α₁
  {-# COMPILE AGDA2HS cut #-}

@0 cutDrop : {α : Scope name} → x ∈ α → Scope name
cutDrop x = fst (cut x)
{-# COMPILE AGDA2HS cutDrop inline #-}

@0 cutTake : {α : Scope name} →  x ∈ α → Scope name
cutTake x = snd (cut x)
{-# COMPILE AGDA2HS cutTake inline #-}

opaque
  unfolding cut Split Scope
  @0 cutEq : (xp : x ∈ α) → cutTake xp <> (x ◃ cutDrop xp) ≡ α
  cutEq {α = iErased ∷ α'} (Zero  ⟨ IsZero  refl ⟩) = refl
  cutEq {α = iErased ∷ α'} (Suc n ⟨ IsSuc p ⟩) = cong (λ α → iErased ∷ α ) (cutEq (n ⟨ p ⟩))

  {- cutSplit without unfolding use SplitRefl and therefore needs Rezz α -}
  cutSplit : (xp : x ∈ α) → cutTake xp ⋈ (x ◃ cutDrop xp) ≡ α
  cutSplit (Zero  ⟨ IsZero  refl ⟩) = EmptyL
  cutSplit (Suc n ⟨ IsSuc p ⟩) = ConsL _ (cutSplit (n ⟨ p ⟩))
  {-# COMPILE AGDA2HS cutSplit #-}

rezzCutDrop : {xp : x ∈ α} → Rezz α → Rezz (cutDrop xp)
rezzCutDrop αRun = rezzUnbind (rezzSplitRight (cutSplit _) αRun)
{-# COMPILE AGDA2HS rezzCutDrop inline #-}

rezzCutTake : {xp : x ∈ α} → Rezz α → Rezz (cutTake xp)
rezzCutTake αRun =  rezzSplitLeft (cutSplit _) αRun
{-# COMPILE AGDA2HS rezzCutTake inline #-}


subCut :  {xp : x ∈ α} → Rezz α → (cutTake xp <> cutDrop xp) ⊆ α
subCut {xp = xp} αRun =
  subst0 (λ α' → (cutTake xp <> cutDrop xp) ⊆ α')
    (cutEq xp) (subJoin (rezzCutTake αRun) subRefl (subBindDrop subRefl))
{-# COMPILE AGDA2HS subCut inline #-}

subCutDrop :  {xp : x ∈ α} →  cutDrop xp ⊆ α
subCutDrop = subTrans (subBindDrop subRefl) (subRight (cutSplit _))
{-# COMPILE AGDA2HS subCutDrop inline #-}

subCutTake :  {xp : x ∈ α} →  cutTake xp ⊆ α
subCutTake = subLeft (cutSplit _)
{-# COMPILE AGDA2HS subCutTake inline #-}
