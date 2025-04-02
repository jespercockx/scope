module Scope.Sub where

open import Haskell.Prelude
open import Haskell.Extra.Erase

open import Scope.Core
open import Scope.Split

private variable
  @0 name : Set
  @0 x y : name
  @0 α α₁ α₂ β β₁ β₂ γ : Scope name

opaque
  Sub : (@0 α β  : Scope name) → Set
  Sub α β = Σ0 _ (λ γ → α ⋈ γ ≡ β)
  {-# COMPILE AGDA2HS Sub inline #-}

  infixr 4 Sub
  syntax Sub α β = α ⊆ β

  subTrans : α ⊆ β → β ⊆ γ → α ⊆ γ
  subTrans < p > < q > =
    let < r , _ > = splitAssoc p q
    in  < r >
  {-# COMPILE AGDA2HS subTrans #-}

  subLeft : α ⋈ β ≡ γ → α ⊆ γ
  subLeft p = < p >
  {-# COMPILE AGDA2HS subLeft transparent #-}

  subRight : α ⋈ β ≡ γ → β ⊆ γ
  subRight p = < splitComm p >
  {-# COMPILE AGDA2HS subRight #-}

  subWeaken : α ⊆ β → α ⊆ β ▸ x
  subWeaken < p > = < splitBindRight p >
  {-# COMPILE AGDA2HS subWeaken #-}

  subEmpty : mempty ⊆ α
  subEmpty = subLeft splitEmptyLeft
  {-# COMPILE AGDA2HS subEmpty #-}

  subRefl : α ⊆ α
  subRefl = subLeft splitEmptyRight
  {-# COMPILE AGDA2HS subRefl #-}

  rezzSub : α ⊆ β → Rezz β → Rezz α
  rezzSub < p > = rezzSplitLeft p
  {-# COMPILE AGDA2HS rezzSub #-}

  subJoin : Rezz β₂
          → α₁ ⊆ α₂
          → β₁ ⊆ β₂
          → (α₁ <> β₁) ⊆ (α₂ <> β₂)
  subJoin r < p > < q > = < splitJoin r p q >
  {-# COMPILE AGDA2HS subJoin #-}

  subJoinKeep : Rezz β → α₁ ⊆ α₂ → (α₁ <> β) ⊆ (α₂ <> β)
  subJoinKeep r < p > = < splitJoinLeft r p >
  {-# COMPILE AGDA2HS subJoinKeep #-}

  subJoinDrop : Rezz β → α₁ ⊆ α₂ → α₁ ⊆ (α₂ <> β)
  subJoinDrop r < p > = < splitJoinRight r p >
  {-# COMPILE AGDA2HS subJoinDrop #-}

  subJoinHere : Rezz β → α₁ ⊆ β → α₁ ⊆ (α₂ <> β)
  subJoinHere r < p > = < splitJoinRightr r p >
  {-# COMPILE AGDA2HS subJoinHere #-}

opaque
  unfolding Sub

  subBindKeep : α ⊆ β → α ▸ y ⊆ β ▸ y
  subBindKeep {y = y} = subJoinKeep (rezz (singleton y))
  {-# COMPILE AGDA2HS subBindKeep #-}

  subBindDrop : α ⊆ β → α ⊆ β ▸ y
  subBindDrop = subWeaken
  {-# COMPILE AGDA2HS subBindDrop #-}

opaque
  unfolding Sub

  joinSubLeft : Rezz α₂ → (α₁ <> α₂) ⊆ β → α₁ ⊆ β
  joinSubLeft r < p > =
    let < q , _ > = splitAssoc (splitRefl r) p
    in  < q >
  {-# COMPILE AGDA2HS joinSubLeft #-}

  joinSubRight : Rezz α₂ → (α₁ <> α₂) ⊆ β → α₂ ⊆ β
  joinSubRight r < p > =
    let < q , _ > = splitAssoc (splitComm (splitRefl r)) p
    in  < q >
  {-# COMPILE AGDA2HS joinSubRight #-}

opaque
  unfolding RScope Sub Split extScope
  subExtScopeKeep : {@0 rγ : RScope name} → Rezz rγ → α ⊆ β → (extScope α rγ) ⊆ (extScope β rγ)
  subExtScopeKeep (rezz []) s = s
  subExtScopeKeep (rezz (Erased x ∷ rγ)) (⟨ δ ⟩ s) = subExtScopeKeep (rezz rγ) (⟨ δ ⟩ (ConsL x s))
  {-# COMPILE AGDA2HS subExtScopeKeep #-}


  subExtScope : {@0 rγ : RScope name} → Rezz rγ → α ⊆ β → α ⊆ (extScope β rγ)
  subExtScope (rezz []) s = s
  subExtScope (rezz (Erased x ∷ rγ)) (⟨ δ ⟩ s) = subExtScope (rezz rγ) (⟨ δ ▸ x ⟩ (ConsR x s))
  {-# COMPILE AGDA2HS subExtScope #-}

opaque
  unfolding Sub subBindKeep joinSubLeft subExtScope
  SubThings : Set₁
  SubThings = Set
