
module Scope.Core where

open import Haskell.Prelude hiding (All; _∘_)

open import Haskell.Law.Semigroup.Def using (IsLawfulSemigroup; associativity)
open import Haskell.Law.Monoid.Def using (IsLawfulMonoid; rightIdentity; leftIdentity; concatenation)
open import Haskell.Extra.Erase

open import Utils.Tactics
import Utils.List as List

private variable
  @0 name : Set

---------------------------------------------------------------------------------------------------
                                     {- PART ONE : Scope -}
---------------------------------------------------------------------------------------------------
module DefScope where
  open import Haskell.Law.List

  opaque
    Scope : (@0 name : Set) → Set
    Scope name = List (Erase name)
    {-# COMPILE AGDA2HS Scope #-}

    singleton : @0 name → Scope name
    singleton x = Erased x ∷ []
    {-# COMPILE AGDA2HS singleton #-}

    syntax singleton x = [ x ]

    instance
      iSemigroupScope : Semigroup (Scope name)
      iSemigroupScope ._<>_ α β = β ++ α

    private
      -- we do this to get a transparent super field in the monoid instance
      scopeMempty : Scope name
      scopeMempty = mempty

      scopeMappend : Scope name → Scope name → Scope name
      scopeMappend α β = mappend β α

      scopeMConcat : List (Scope name) → Scope name
      scopeMConcat [] = mempty
      scopeMConcat (x ∷ xs) = (scopeMConcat xs) ++ x

  instance
    iMonoidScope : Monoid (Scope name)
    Monoid.super iMonoidScope = iSemigroupScope
    Monoid.mempty iMonoidScope = scopeMempty
    Monoid.mappend iMonoidScope = scopeMappend
    Monoid.mconcat iMonoidScope = scopeMConcat

  opaque
    unfolding Scope
    instance
      iLawfulSemigroupScope : IsLawfulSemigroup (Scope name)
      iLawfulSemigroupScope .associativity _       _  []  = refl
      iLawfulSemigroupScope .associativity xs ys (z ∷ zs)
        rewrite (++-assoc zs ys xs)
        = refl

      iLawfulMonoidScope : IsLawfulMonoid (Scope name)
      iLawfulMonoidScope .rightIdentity [] = refl
      iLawfulMonoidScope .rightIdentity (x ∷ xs)
        rewrite ++-[] (x ∷ xs)
        = refl

      iLawfulMonoidScope .leftIdentity [] = refl
      iLawfulMonoidScope .leftIdentity (x ∷ xs)
        rewrite ++-[] (x ∷ xs)
        = refl

      iLawfulMonoidScope .concatenation [] = refl
      iLawfulMonoidScope .concatenation (x ∷ xs)
        rewrite ++-[] (x ∷ xs)
          | concatenation ⦃ iMonoidA = iMonoidScope ⦄ xs
        = refl

  bind : Scope name → @0 name  → Scope name
  bind α x = α <> [ x ]
  {-# COMPILE AGDA2HS bind #-}

  infixl 5 bind
  syntax bind α x = α ▸ x

{- end of module DefScope -}
open DefScope public

-- bindr : Scope name → @0 name → Scope name
-- bindr α x = α <> [ x ]
-- {-# COMPILE AGDA2HS bindr #-}

-- infixr 5 bindr
-- syntax bindr α x = α ▹ x

---------------------------------------------------------------------------------------------------
                                    {- PART TWO : RScope -}
---------------------------------------------------------------------------------------------------
module DefRScope where
  open import Haskell.Law.Monoid.List using (iLawfulMonoidList)
  open import Haskell.Law.Semigroup.List using (iLawfulSemigroupList)

  opaque
    RScope : (@0 name : Set) → Set
    RScope name = List (Erase name)
    {-# COMPILE AGDA2HS RScope #-}

    rsingleton : @0 name → RScope name
    rsingleton x = Erased x ∷ []
    {-# COMPILE AGDA2HS rsingleton #-}

    syntax rsingleton x = x ◂

    instance
      iSemigroupRScope : Semigroup (RScope name)
      iSemigroupRScope ._<>_ = _++_

    private
      -- we do this to get a transparent super field in the monoid instance
      rscopeMempty : RScope name
      rscopeMempty = mempty

      rscopeMappend : RScope name → RScope name → RScope name
      rscopeMappend = mappend

      rscopeMConcat : List (RScope name) → RScope name
      rscopeMConcat = mconcat

  instance
    iMonoidRScope : Monoid (RScope name)
    Monoid.super iMonoidRScope = iSemigroupRScope
    Monoid.mempty iMonoidRScope = rscopeMempty
    Monoid.mappend iMonoidRScope = rscopeMappend
    Monoid.mconcat iMonoidRScope = rscopeMConcat

  opaque
    unfolding RScope
    instance
      iLawfulSemigroupRScope : IsLawfulSemigroup (RScope name)
      iLawfulSemigroupRScope = iLawfulSemigroupList

      iLawfulMonoidRScope : IsLawfulMonoid (RScope name)
      iLawfulMonoidRScope = iLawfulMonoidList

  rbind : @0 name → RScope name → RScope name
  rbind x α = x ◂ <> α
  {-# COMPILE AGDA2HS rbind #-}

  infixr 5 rbind
  syntax rbind x α = x ◂ α

{- end of module DefRScope -}
open DefRScope public

---------------------------------------------------------------------------------------------------
                                {- PART THREE : Combinations -}
---------------------------------------------------------------------------------------------------
module Combinations where
  open import Haskell.Law.Equality

  opaque
    unfolding RScope

    extScope : Scope name → RScope name → Scope name
    extScope s [] = s
    extScope α (Erased x ∷ rs) = extScope (α ▸ x) rs
    {-# COMPILE AGDA2HS extScope #-}

    extScopeEmpty : {α : Scope name} → (extScope α mempty) ≡ α
    extScopeEmpty = refl

    extScopeBind : {α : Scope name} {y : name} {rγ : RScope name} → extScope α (y ◂ rγ) ≡ extScope (α ▸ y) rγ
    extScopeBind = refl

    @0 extScopeConcatBind : (@0 α : Scope name) (@0 y : name) (@0 rγ : RScope name) → (extScope (α ▸ y) rγ) ≡ α <> (extScope [ y ] rγ)
    extScopeConcatBind  α y [] = refl
    extScopeConcatBind  α y (Erased z ∷ rγ) =
      let e₀ : (extScope (α ▸ y) (z ◂ rγ)) ≡ (α ▸ y) <> (extScope [ z ] rγ)
          e₀ = extScopeConcatBind (α ▸ y) z rγ
          e₁ : (α <> [ y ]) <> (extScope [ z ] rγ) ≡  α <> ([ y ] <> (extScope [ z ] rγ))
          e₁ = sym (associativity α [ y ] (extScope [ z ] rγ))
          e₂ : (extScope ([ y ] ▸ z) rγ) ≡ [ y ] <> (extScope [ z ] rγ)
          e₂ = extScopeConcatBind [ y ] z rγ
      in
      trans (trans e₀ e₁) (sym (cong (λ δ → α <> δ) e₂))

  opaque
    unfolding Scope extScope
    @0 extScopeConcatEmpty : (@0 α : Scope name) (@0 rγ : RScope name) → (extScope α rγ) ≡ α <> (extScope mempty rγ)
    extScopeConcatEmpty  α [] = refl
    extScopeConcatEmpty α (Erased z ∷ rγ) = extScopeConcatBind α z rγ

    @0 extScopeConcat : (@0 α β : Scope name) (@0 rγ : RScope name) → (extScope (α <> β) rγ) ≡ α <> (extScope β rγ)
    extScopeConcat α [] rγ =
      extScopeConcatEmpty α rγ
    extScopeConcat α (Erased y ∷ β) rγ =
      extScopeConcat α β (y ◂ rγ)

  opaque
    unfolding extScope
    rezzExtScope : {@0 α : Scope name} {@0 rβ : RScope name}
      → Rezz α → Rezz rβ → Rezz (extScope α rβ)
    rezzExtScope αRun (rezz []) = αRun
    rezzExtScope (rezz α) (rezz (Erased x ∷ rβ)) = rezzExtScope (rezz (α ▸ x)) (rezz rβ)
    {-# COMPILE AGDA2HS rezzExtScope #-}

{- end of module Combinations -}
open Combinations public


opaque
  unfolding Scope

  caseScope : (α : Scope name)
            → (@0 {{α ≡ mempty}} → c)
            → ((@0 x : name) (β : Scope name) → @0 {{α ≡ β ▸ x}} → c)
            → c
  caseScope [] emptyCase bindCase = emptyCase
  caseScope (Erased x ∷ β) emptyCase bindCase = bindCase x β
  {-# COMPILE AGDA2HS caseScope #-}

opaque
  unfolding RScope

  caseRScope : (rα : RScope name)
            → (@0 {{rα ≡ mempty}} → c)
            → ((@0 x : name) (rβ : RScope name) → @0 {{rα ≡ x ◂ rβ}} → c)
            → c
  caseRScope [] emptyCase bindCase = emptyCase
  caseRScope (Erased x ∷ β) emptyCase bindCase = bindCase x β
  {-# COMPILE AGDA2HS caseRScope #-}

opaque
  unfolding Scope
  rezzBind
    : {@0 α : Scope name} {@0 x : name}
    → Rezz α → Rezz (bind α x)
  rezzBind = rezzCong2 _∷_ rezzErase
  {-# COMPILE AGDA2HS rezzBind #-}

  rezzUnbind : {@0 x : name} {@0 α : Scope name} → Rezz (α ▸ x) → Rezz α
  rezzUnbind = rezzTail
  {-# COMPILE AGDA2HS rezzUnbind #-}

opaque
  unfolding Scope iLawfulMonoidScope RScope iLawfulMonoidRScope extScope extScopeConcatEmpty rezzExtScope caseScope caseRScope rezzBind
  ScopeCoreThings : Set₁
  ScopeCoreThings = Set
 