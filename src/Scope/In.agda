module Scope.In where

open import Haskell.Prelude hiding (coerce)

open import Haskell.Extra.Dec
open import Haskell.Extra.Erase
open import Haskell.Extra.Refinement
open import Haskell.Law.Equality

open import Utils.Misc

open import Scope.Core
open import Scope.Split
open import Scope.Sub

private variable
  @0 name : Set
  @0 x y : name
  @0 α β γ : Scope name

data IsNth (@0 x : name) : @0 Scope name → Nat → Set where
  IsZero : x ≡ y → IsNth x (y ◃ α) zero
  IsSuc : {n : Nat} → IsNth x α n → IsNth x (y ◃ α) (suc n)

inScope : @0 name → @0 Scope name → Set
inScope x α = ∃ Nat (λ n → IsNth x α n)
{-# COMPILE AGDA2HS inScope #-}

syntax inScope x α = x ∈ α

inToSub : x ∈ α → [ x ] ⊆ α
inToSub {x = x} (zero ⟨ IsZero refl ⟩) = subLeft (splitRefl (rezz [ x ]))
inToSub (suc n ⟨ IsSuc p ⟩) = subBindDrop (inToSub (n ⟨ p ⟩))
{-# COMPILE AGDA2HS inToSub inline #-}

opaque
  unfolding Sub Split
  subToIn : [ x ] ⊆ α → x ∈ α
  subToIn < EmptyR > = zero ⟨ IsZero refl ⟩
  subToIn < ConsL _ _ > = zero ⟨ IsZero refl ⟩
  subToIn < ConsR _ p > = do
    let n ⟨ np ⟩ = subToIn < p >
    suc n ⟨ IsSuc np ⟩
  {-# COMPILE AGDA2HS subToIn inline #-}

opaque
  unfolding Sub Split
  coerce : α ⊆ β → x ∈ α → x ∈ β
  coerce < EmptyR > p = p
  coerce < ConsL _ _ > (zero ⟨ IsZero refl ⟩) = zero ⟨ IsZero refl ⟩
  coerce < ConsL _ j > (suc n ⟨ IsSuc p ⟩) = do
    let n' ⟨ p' ⟩ = coerce < j > (n ⟨ p ⟩)
    suc n' ⟨ IsSuc p' ⟩
  coerce (⟨ _ ⟩ ConsR _ j) (n ⟨ p ⟩) = do
    let n' ⟨ p' ⟩ = coerce < j > (n ⟨ p ⟩)
    suc n' ⟨ IsSuc p' ⟩
  {-# COMPILE AGDA2HS coerce inline #-}

opaque

  inHere : x ∈ (x ◃ α)
  inHere = zero ⟨ IsZero refl ⟩
  {-# COMPILE AGDA2HS inHere #-}

  inThere : x ∈ α → x ∈ (y ◃ α)
  inThere (n ⟨ p ⟩) = suc n ⟨ IsSuc p ⟩
  {-# COMPILE AGDA2HS inThere #-}

  bindSubToIn : (x ◃ α) ⊆ β → x ∈ β
  bindSubToIn s = coerce s inHere
  {-# COMPILE AGDA2HS bindSubToIn #-}

opaque
  unfolding Split

  @0 inEmptyToBot : x ∈ mempty → ⊥
  inEmptyToBot ()

  inEmptyCase : @0 (x ∈ mempty) → a
  inEmptyCase p = error {i = inEmptyToBot p} "impossible"
  {-# COMPILE AGDA2HS inEmptyCase #-}

  inSingCase : x ∈ [ y ] → (@0 x ≡ y → a) → a
  inSingCase (zero ⟨ IsZero refl ⟩) f = f refl
  inSingCase (suc n ⟨ IsSuc () ⟩) f
  {-# COMPILE AGDA2HS inSingCase #-}

  inSplitCase : α ⋈ β ≡ γ → x ∈ γ → (x ∈ α → a) → (x ∈ β → a) → a
  inSplitCase EmptyL (zero ⟨ IsZero refl ⟩) f g = g inHere
  inSplitCase EmptyL (suc n ⟨ IsSuc p ⟩) f g = g (inThere (n ⟨ p ⟩))
  inSplitCase EmptyR (zero ⟨ IsZero refl ⟩) f g = f inHere
  inSplitCase EmptyR (suc n ⟨ IsSuc p ⟩) f g = f (inThere (n ⟨ p ⟩))
  inSplitCase (ConsL _ j) (zero ⟨ IsZero refl ⟩) f g = f inHere
  inSplitCase (ConsL _ j) (suc n ⟨ IsSuc p ⟩) f g = inSplitCase j (n ⟨ p ⟩) (f ∘ inThere) g
  inSplitCase (ConsR _ j) (zero ⟨ IsZero refl ⟩) f g = g inHere
  inSplitCase (ConsR _ j) (suc n ⟨ IsSuc p ⟩) f g = inSplitCase j (n ⟨ p ⟩) f (g ∘ inThere)
  {-# COMPILE AGDA2HS inSplitCase #-}

opaque
  inJoinCase
    : Rezz α
    → x ∈ (α <> β) → (x ∈ α → a) → (x ∈ β → a) → a
  inJoinCase r = inSplitCase (splitRefl r)
  {-# COMPILE AGDA2HS inJoinCase #-}

opaque
  inBindCase : x ∈ (y ◃ α) → (@0 x ≡ y → a) → (x ∈ α → a) → a
  inBindCase {y = y} p f g = inJoinCase (rezz [ y ]) p (λ q → (inSingCase q f)) g
  {-# COMPILE AGDA2HS inBindCase #-}

  inBindrCase : Rezz α → x ∈ (α ▹ y) → (x ∈ α → a) → (@0 x ≡ y → a) → a
  inBindrCase r p f g = inJoinCase r p f (λ q → inSingCase q g)
  {-# COMPILE AGDA2HS inBindrCase #-}

opaque
  unfolding Scope

  decIn
    : {@0 x y : name} (p : x ∈ α) (q : y ∈ α)
    → Dec (_≡_ {A = Σ0 name (λ n → n ∈ α)} (⟨ x ⟩ p) (⟨ y ⟩ q))
  decIn (zero ⟨ IsZero refl ⟩) (zero ⟨ IsZero refl ⟩) = True ⟨ refl ⟩
  decIn (zero ⟨ _ ⟩) (suc m ⟨ _ ⟩) = False ⟨ (λ ()) ⟩
  decIn (suc n ⟨ _ ⟩) (zero ⟨ _ ⟩) = False ⟨ (λ ()) ⟩
  decIn (suc n ⟨ IsSuc p ⟩) (suc m ⟨ IsSuc q ⟩) = mapDec aux (λ where refl → refl) (decIn (n ⟨ p ⟩) (m ⟨ q ⟩))
    where
      @0 aux : ∀ {@0 x y z γ n m} {p : IsNth x γ n} {q : IsNth y γ m} →
            _≡_ {A = Σ0 name (λ w → w ∈ γ)} (⟨ x ⟩ n ⟨ p ⟩) (⟨ y ⟩ m ⟨ q ⟩) →
            _≡_ {A = Σ0 name (λ w → w ∈ (Erased z ∷ γ))}
               (⟨ x ⟩ suc n ⟨ IsSuc p ⟩)
               (⟨ y ⟩ suc m ⟨ IsSuc q ⟩)
      aux refl = refl
  {-# COMPILE AGDA2HS decIn #-}

opaque
  unfolding inHere inEmptyCase inJoinCase inBindCase inBindrCase decIn
  InThings : Set₁
  InThings = Set
