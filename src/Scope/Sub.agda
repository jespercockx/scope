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

  subWeaken : α ⊆ β → α ⊆ (bind x β)
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

  subJoin : Rezz α₂
          → α₁ ⊆ α₂
          → β₁ ⊆ β₂
          → (α₁ <> β₁) ⊆ (α₂ <> β₂)
  subJoin r < p > < q > = < splitJoin r p q >
  {-# COMPILE AGDA2HS subJoin #-}

  subJoinKeep : Rezz α → β₁ ⊆ β₂ → (α <> β₁) ⊆ (α <> β₂)
  subJoinKeep r < p > = < splitJoinLeft r p >
  {-# COMPILE AGDA2HS subJoinKeep #-}

  subJoinDrop : Rezz α → β₁ ⊆ β₂ → β₁ ⊆ (α <> β₂)
  subJoinDrop r < p > = < splitJoinRight r p >
  {-# COMPILE AGDA2HS subJoinDrop #-}

  subJoinHere : Rezz α₂ → α₁ ⊆ α₂ → α₁ ⊆ (α₂ <> β)
  subJoinHere r < p > = < splitJoinRightr r p >
  {-# COMPILE AGDA2HS subJoinHere #-}

opaque
  unfolding Sub

  subBindKeep : α ⊆ β → (bind y α) ⊆ (bind y β)
  subBindKeep {y = y} = subJoinKeep (rezz (singleton y))
  {-# COMPILE AGDA2HS subBindKeep #-}

  subBindDrop : α ⊆ β → α ⊆ (bind y β)
  subBindDrop {y = y} = subJoinDrop (rezz (singleton y))
  {-# COMPILE AGDA2HS subBindDrop #-}

  subBindrKeep : Rezz β → α ⊆ β → (bindr α y) ⊆ (bindr β y)
  subBindrKeep {y = y} r < p > = < splitBindrLeft r p >
  {-# COMPILE AGDA2HS subBindrKeep #-}

  subBindrDrop : Rezz β → α ⊆ β → α ⊆ (bindr β y)
  subBindrDrop {y = y} r < p > = < splitBindrRight r p >
  {-# COMPILE AGDA2HS subBindrDrop #-}

opaque
  unfolding Sub

  joinSubLeft : Rezz α₁ → (α₁ <> α₂) ⊆ β → α₁ ⊆ β
  joinSubLeft r < p > =
    let < q , _ > = splitAssoc (splitRefl r) p
    in  < q >
  {-# COMPILE AGDA2HS joinSubLeft #-}

  joinSubRight : Rezz α₁ → (α₁ <> α₂) ⊆ β → α₂ ⊆ β
  joinSubRight r < p > =
    let < q , _ > = splitAssoc (splitComm (splitRefl r)) p
    in  < q >
  {-# COMPILE AGDA2HS joinSubRight #-}

opaque
  unfolding Sub Split
  subExtScopeKeep : {@0 rγ : RScope name} → Rezz rγ → α ⊆ β → (extScope α rγ) ⊆ (extScope β rγ)
  subExtScopeKeep (rezz Nil) s = s
  subExtScopeKeep (rezz (x ◂ rγ)) (⟨ δ ⟩ s) = subExtScopeKeep (rezz rγ) (⟨ δ ⟩ (ConsL x s))

  subExtScope : {@0 rγ : RScope name} → Rezz rγ → α ⊆ β → α ⊆ (extScope β rγ)
  subExtScope (rezz Nil) s = s
  subExtScope (rezz (x ◂ rγ)) (⟨ δ ⟩ s) = subExtScope (rezz rγ) (⟨ x ◃ δ ⟩ (ConsR x s))
opaque
  unfolding Sub subBindKeep joinSubLeft
  SubThings : Set₁
  SubThings = Set
