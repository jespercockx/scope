module Scope.Renaming where

open import Haskell.Prelude hiding (coerce)

open import Haskell.Extra.Erase
open import Haskell.Extra.Refinement
open import Haskell.Law.Equality

open import Scope.Core
open import Scope.Sub
open import Scope.In
open import Scope.Diff

private variable
  @0 name : Set
  @0 α β : Scope name

{-
data Permutation {@0 name : Set} : (@0 α β : Scope name) → Set where
  PNil : Permutation mempty mempty
  PCons : {@0 x : name}
    (xp : x ∈ β)
    → Permutation α (β \[ xp ])
    → Permutation  (x ◃ α) β
{-# COMPILE AGDA2HS Permutation deriving Show #-}

pattern ⌈⌉ = PNil
infix 6 ⌈_~>_◃_⌉
pattern ⌈_~>_◃_⌉ x xp σ = PCons {x = x} xp σ
infix 4 ⌈_~>_◃⌉
pattern ⌈_~>_◃⌉ x xp = ⌈ x ~> xp ◃ ⌈⌉ ⌉
-}

Renaming : (@0 α β : Scope name) → Set
Renaming {name = name} α β = {@0 x : name} → x ∈ α → x ∈ β
{-# COMPILE AGDA2HS Renaming inline #-}

opaque
  unfolding Scope
  @0 RenamingInEmpty : ∀ {@0 α : Scope name} → Renaming α mempty → α ≡ mempty
  RenamingInEmpty {α = []} r = refl
  RenamingInEmpty {α = x ∷ α} r = inEmptyCase (r inHere)

{-
opaque
  unfolding Scope
  permutationToRenaming : ∀ {@0 α β : Scope name} → Permutation α β → Renaming α β
  permutationToRenaming ⌈⌉ = id
  permutationToRenaming ⌈ x ~> xp ◃ _ ⌉ (Zero ⟨ IsZero refl ⟩) = xp
  permutationToRenaming ⌈ x ~> xp ◃ p ⌉ (Suc n ⟨ IsSuc np ⟩) =
    let res = permutationToRenaming p  (n ⟨ np ⟩) in
    (coerce (diffSub (inToSub xp)) res)
  {-# COMPILE AGDA2HS permutationToRenaming #-}

opaque
  permutationToRenamingRev : ∀ {@0 α β : Scope name} → Permutation α β → Renaming β α
  permutationToRenamingRev ⌈⌉ = id
  permutationToRenamingRev ⌈ x ~> xp ◃ p ⌉ yp =
    diffVarCase yp xp
      (λ refl → Zero ⟨ IsZero refl ⟩ )
      (λ yp' → let res = permutationToRenamingRev p yp' in (inThere res))
  {-# COMPILE AGDA2HS permutationToRenamingRev #-}

opaque
  unfolding Scope diff
  idPerm : Rezz α → Permutation α α
  idPerm (rezz []) = ⌈⌉
  idPerm (rezz (Erased x ∷ α)) = ⌈ x ~> Zero ⟨ IsZero refl ⟩ ◃ idPerm (rezz α) ⌉
  {-# COMPILE AGDA2HS idPerm inline #-}

-}
