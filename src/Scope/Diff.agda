module Scope.Diff where

open import Haskell.Prelude hiding (coerce)
open import Haskell.Extra.Erase

open import Scope.Core
open import Scope.Split
open import Scope.Sub
open import Scope.In

private variable
  @0 name : Set
  @0 x y : name
  @0 α α₁ α₂ β β₁ β₂ γ : Scope name

opaque
  unfolding Sub

  @0 diff : ∀ {α β : Scope name} → α ⊆ β → Scope name
  diff (⟨ p ⟩ _) = p

  @0 diffVar : ∀ {α : Scope name} → x ∈ α → Scope name
  diffVar xp = diff (inToSub xp)

  syntax diffVar {α = α} xp = α \[ xp ]

  diff-left : (p : α ⋈ β ≡ γ) → diff (subLeft p) ≡ β
  diff-left p = refl

  diff-right : (p : α ⋈ β ≡ γ) → diff (subRight p) ≡ α
  diff-right p = refl

  splitDiff : (p : α ⊆ β) → α ⋈ diff p ≡ β
  splitDiff p = proj₂ p
  {-# COMPILE AGDA2HS splitDiff transparent #-}

  diffSub : (p : α ⊆ β) → diff p ⊆ β
  diffSub p = subRight (splitDiff p)
  {-# COMPILE AGDA2HS diffSub inline #-}

  diffCase : (p : α ⊆ β) → x ∈ β
            → (x ∈ α → a) → (x ∈ diff p → a) → a
  diffCase p = inSplitCase (splitDiff p)
  {-# COMPILE AGDA2HS diffCase inline #-}

opaque
  unfolding diff

  diffSubTrans : (p : α ⊆ β) (q : β ⊆ γ) → diff p ⊆ diff (subTrans p q)
  diffSubTrans < p > < q > =
    let < _ , s > = splitAssoc p q
    in  < s >
  {-# COMPILE AGDA2HS diffSubTrans #-}

diffCoerce : (p : α ⊆ β) (q : x ∈ α) → diff (inToSub q) ⊆ diff (subTrans (inToSub q) p)
diffCoerce p q = diffSubTrans (inToSub q) p
{-# COMPILE AGDA2HS diffCoerce inline #-}

opaque
  unfolding diff diffSubTrans
  DiffThings : Set₁
  DiffThings = Set
