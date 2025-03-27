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
  @0 rβ : RScope name

data Index : Set where
  Zero : Index
  Suc : Index → Index
{-# COMPILE AGDA2HS Index deriving Show #-}


data IsNth (@0 x : name) : @0 Scope name → Index → Set where
  IsZero : x ≡ y → IsNth x (α ▸ y) Zero
  IsSuc : {n : Index} → IsNth x α n → IsNth x (α ▸ y) (Suc n)

In : @0 name → @0 Scope name → Set
In x α = ∃ Index (λ n → IsNth x α n)
{-# COMPILE AGDA2HS In inline #-}

infix 6 In
syntax In x α = x ∈ α

inToSub : x ∈ α → [ x ] ⊆ α
inToSub {x = x} (Zero ⟨ IsZero refl ⟩) = subRight (splitRefl (rezz [ x ]))
inToSub (Suc n ⟨ IsSuc p ⟩) = subBindDrop (inToSub (n ⟨ p ⟩))
{-# COMPILE AGDA2HS inToSub #-}

opaque
  unfolding Sub Split
  subToIn : [ x ] ⊆ α → x ∈ α
  subToIn < EmptyR > = Zero ⟨ IsZero refl ⟩
  subToIn < ConsL _ _ > = Zero ⟨ IsZero refl ⟩
  subToIn < ConsR _ p > = do
    let n ⟨ np ⟩ = subToIn < p >
    Suc n ⟨ IsSuc np ⟩
  {-# COMPILE AGDA2HS subToIn #-}

opaque
  unfolding Sub Split
  coerce : α ⊆ β → x ∈ α → x ∈ β
  coerce < EmptyR > p = p
  coerce < ConsL _ _ > (Zero ⟨ IsZero refl ⟩) = Zero ⟨ IsZero refl ⟩
  coerce < ConsL _ j > (Suc n ⟨ IsSuc p ⟩) = do
    let n' ⟨ p' ⟩ = coerce < j > (n ⟨ p ⟩)
    Suc n' ⟨ IsSuc p' ⟩
  coerce (⟨ _ ⟩ ConsR _ j) (n ⟨ p ⟩) = do
    let n' ⟨ p' ⟩ = coerce < j > (n ⟨ p ⟩)
    Suc n' ⟨ IsSuc p' ⟩
  {-# COMPILE AGDA2HS coerce #-}

opaque

  inHere : x ∈ (α ▸ x)
  inHere = Zero ⟨ IsZero refl ⟩
  {-# COMPILE AGDA2HS inHere #-}

  inThere : x ∈ α → x ∈ (α ▸ y)
  inThere (n ⟨ p ⟩) = Suc n ⟨ IsSuc p ⟩
  {-# COMPILE AGDA2HS inThere #-}

  bindSubToIn : (α ▸ x) ⊆ β → x ∈ β
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
  inSingCase (Zero ⟨ IsZero refl ⟩) f = f refl
  inSingCase (Suc n ⟨ IsSuc () ⟩) f
  {-# COMPILE AGDA2HS inSingCase #-}

  inSplitCase : α ⋈ β ≡ γ → x ∈ γ → (x ∈ α → a) → (x ∈ β → a) → a
  inSplitCase EmptyL (Zero ⟨ IsZero refl ⟩) f g = g inHere
  inSplitCase EmptyL (Suc n ⟨ IsSuc p ⟩) f g = g (inThere (n ⟨ p ⟩))
  inSplitCase EmptyR (Zero ⟨ IsZero refl ⟩) f g = f inHere
  inSplitCase EmptyR (Suc n ⟨ IsSuc p ⟩) f g = f (inThere (n ⟨ p ⟩))
  inSplitCase (ConsL _ j) (Zero ⟨ IsZero refl ⟩) f g = f inHere
  inSplitCase (ConsL _ j) (Suc n ⟨ IsSuc p ⟩) f g = inSplitCase j (n ⟨ p ⟩) (f ∘ inThere) g
  inSplitCase (ConsR _ j) (Zero ⟨ IsZero refl ⟩) f g = g inHere
  inSplitCase (ConsR _ j) (Suc n ⟨ IsSuc p ⟩) f g = inSplitCase j (n ⟨ p ⟩) f (g ∘ inThere)
  {-# COMPILE AGDA2HS inSplitCase #-}

opaque
  inJoinCase
    : Rezz β
    → x ∈ (α <> β) → (x ∈ α → a) → (x ∈ β → a) → a
  inJoinCase r = inSplitCase (splitRefl r)
  {-# COMPILE AGDA2HS inJoinCase #-}

opaque
  inBindCase : x ∈ (α ▸ y) → (x ∈ α → a) → (@0 x ≡ y → a) → a
  inBindCase {α = α} {y = y} p g f = inJoinCase (rezz ([ y ])) p g ((λ q → (inSingCase q f)))
  {-# COMPILE AGDA2HS inBindCase #-}

  -- inBindrCase : Rezz α → x ∈ (α ▹ y) → (x ∈ α → a) → (@0 x ≡ y → a) → a
  -- inBindrCase r p f g = inJoinCase r p f (λ q → inSingCase q g)
  -- {-# COMPILE AGDA2HS inBindrCase #-}

inScopeInExtScope : Rezz rβ → x ∈ α → x ∈ (extScope α rβ)
inScopeInExtScope r = coerce (subExtScope r subRefl)

opaque
  unfolding Scope

  decIn
    : {@0 x y : name} (p : x ∈ α) (q : y ∈ α)
    → Dec (_≡_ {A = Σ0 name (λ n → n ∈ α)} (⟨ x ⟩ p) (⟨ y ⟩ q))
  decIn (Zero ⟨ IsZero refl ⟩) (Zero ⟨ IsZero refl ⟩) = True ⟨ refl ⟩
  decIn (Zero ⟨ _ ⟩) (Suc m ⟨ _ ⟩) = False ⟨ (λ ()) ⟩
  decIn (Suc n ⟨ _ ⟩) (Zero ⟨ _ ⟩) = False ⟨ (λ ()) ⟩
  decIn (Suc n ⟨ IsSuc p ⟩) (Suc m ⟨ IsSuc q ⟩) = mapDec aux (λ where refl → refl) (decIn (n ⟨ p ⟩) (m ⟨ q ⟩))
    where
      @0 aux : ∀ {@0 x y z γ n m} {p : IsNth x γ n} {q : IsNth y γ m} →
            _≡_ {A = Σ0 name (λ w → w ∈ γ)} (⟨ x ⟩ n ⟨ p ⟩) (⟨ y ⟩ m ⟨ q ⟩) →
            _≡_ {A = Σ0 name (λ w → w ∈ (Erased z ∷ γ))}
               (⟨ x ⟩ Suc n ⟨ IsSuc p ⟩)
               (⟨ y ⟩ Suc m ⟨ IsSuc q ⟩)
      aux refl = refl
  {-# COMPILE AGDA2HS decIn #-}

opaque
  unfolding subToIn coerce inHere inEmptyCase inJoinCase inBindCase decIn
  InThings : Set₁
  InThings = Set
