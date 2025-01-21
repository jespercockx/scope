module Scope.Renaming where

open import Haskell.Prelude hiding (coerce)

open import Haskell.Extra.Erase
open import Haskell.Extra.Refinement

open import Scope.Core
open import Scope.In
open import Scope.Diff

private variable
  @0 name : Set
  @0 α β : Scope name

NameIn : (@0 α : Scope name) → Set
NameIn α = Σ0 _ λ x → x ∈ α
{-# COMPILE AGDA2HS NameIn inline #-}


data Permutation {@0 name : Set} : (@0 α β : Scope name) → Set where
  PNil : Permutation mempty mempty
  PCons :
    ((⟨ x ⟩ xp) : NameIn β)
    → Permutation α (β \[ xp ])
    → Permutation  (x ◃ α) β
{-# COMPILE AGDA2HS Permutation deriving Show #-}

{-
data PermutationOld {@0 name : Set} : (@0 α β : Scope name) → Set where
  PNil : PermutationOld mempty mempty
  PCons :
    ((⟨ x ⟩ xp) : NameIn α)
    → PermutationOld (α \[ xp ]) β
    → PermutationOld  α (x ◃ β)
{-# COMPILE AGDA2HS PermutationOld deriving Show #-}
-}

pattern ⌈⌉ = PNil
infix 6 ⌈_◃_⌉
pattern ⌈_◃_⌉ x σ = PCons x σ
infix 4 ⌈_◃⌉
pattern ⌈_◃⌉ x = ⌈ x ◃ ⌈⌉ ⌉

Renaming : Scope name → Scope name → Set
Renaming α β = NameIn α → NameIn β
{-# COMPILE AGDA2HS Renaming inline #-}

opaque
  unfolding Scope
  permutationToRenaming : ∀ {@0 α β : Scope name} → Permutation α β → Renaming α β
  permutationToRenaming ⌈⌉ = id
  permutationToRenaming ⌈ xVar ◃ _ ⌉ (⟨ _ ⟩ (Zero ⟨ IsZero refl ⟩)) = xVar
  permutationToRenaming ⌈ ⟨ _ ⟩ xp ◃ p ⌉ (⟨ _ ⟩ (Suc n ⟨ IsSuc np ⟩)) =
    let ⟨ _ ⟩ res = permutationToRenaming p < n ⟨ np ⟩ > in
    < coerce (diffSub (inToSub xp)) res >
  {-# COMPILE AGDA2HS permutationToRenaming #-}

opaque
  unfolding diff
  permutationToRenamingRev : ∀ {@0 α β : Scope name} → Permutation α β → Renaming β α
  permutationToRenamingRev ⌈⌉ = id
  permutationToRenamingRev ⌈ ⟨ _ ⟩ xp ◃ p ⌉ (⟨ _ ⟩ yp) =
    diffCase (inToSub xp) yp
      (λ _ → < Zero ⟨ IsZero refl ⟩ >)
      (λ yp' → let ⟨ _ ⟩ res = permutationToRenamingRev p < yp' > in  < inThere res >)
  {-# COMPILE AGDA2HS permutationToRenamingRev #-}