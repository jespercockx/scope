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
    ((⟨ x ⟩ xp) : NameIn α)
    → Permutation (α \[ xp ]) β
    → Permutation  α (x ◃ β)
{-# COMPILE AGDA2HS Permutation deriving Show #-}


pattern ⌈⌉ = PNil
infix 6 ⌈_◃_⌉
pattern ⌈_◃_⌉ x σ = PCons x σ
infix 4 ⌈_◃⌉
pattern ⌈_◃⌉ x = ⌈ x ◃ ⌈⌉ ⌉

Renaming : Scope name → Scope name → Set
Renaming α β = NameIn α → NameIn β
{-# COMPILE AGDA2HS Renaming inline #-}

opaque
  unfolding Scope diff

  permutationToRenaming : ∀ {@0 α β : Scope name} → Permutation α β → Renaming α β
  permutationToRenaming ⌈⌉ = id
  permutationToRenaming ⌈ xVar ◃ p ⌉ yVar =
    let ⟨ _ ⟩ xp = xVar in
    let ⟨ _ ⟩ yp = yVar in
    diffCase (inToSub xp) yp
      (λ _ → < Zero ⟨ IsZero refl ⟩ >)
      (λ yp' → let ⟨ _ ⟩ res = permutationToRenaming p < yp' > in  < inThere res >)
  {-# COMPILE AGDA2HS permutationToRenaming #-}