module Scope.All where

open import Haskell.Prelude hiding (All)
open import Haskell.Extra.Erase
open import Haskell.Extra.Refinement
open import Haskell.Prim.Tuple using (second)

import Utils.List as List
open import Utils.Tactics

open import Scope.Core
open import Scope.In
open import Scope.Sub
open import Scope.Split

private variable
  @0 name : Set
  @0 α β  : Scope name
  @0 x    : name
  p q     : @0 name → Set

opaque
  unfolding Scope

  All : (p : @0 name → Set) → @0 Scope name → Set
  All p = List.All λ x → p (get x)
  {-# COMPILE AGDA2HS All #-}

  allEmpty : All p mempty
  allEmpty = List.ANil
  {-# COMPILE AGDA2HS allEmpty #-}

  allSingl : p x → All p [ x ]
  allSingl p = List.ACons p List.ANil
  {-# COMPILE AGDA2HS allSingl #-}

  getAllSingl : All p [ x ] → p x
  getAllSingl (List.ACons p List.ANil) = p
  {-# COMPILE AGDA2HS getAllSingl #-}

  allJoin : All p α → All p β → All p (α <> β)
  allJoin List.ANil pbs = pbs
  allJoin (List.ACons px pas) pbs = List.ACons px (allJoin pas pbs)
  {-# COMPILE AGDA2HS allJoin #-}

opaque
  unfolding All Sub Split

  lookupAll : All p α → x ∈ α → p x
  lookupAll ps                < EmptyR    > = getAllSingl ps
  lookupAll (List.ACons px _) < ConsL x _ > = px
  lookupAll (List.ACons _ ps) < ConsR x q > = lookupAll ps < q >
  {-# COMPILE AGDA2HS lookupAll #-}

  findAll : {q : Set}
          → All p α
          → ({@0 el : name} → (pel : p el) → (ela : el ∈ α) → Maybe q)
          → Maybe q
  findAll List.ANil qc = Nothing
  findAll (List.ACons px al) qc =
    case qc px (inHere) of λ where
      (Just qt) → Just qt
      Nothing → findAll al (λ pel i → qc pel (inThere i))
  {-# COMPILE AGDA2HS findAll #-}

_!_ : {p : @0 name → Set} {@0 α : Scope name}
    → All p α → (@0 x : name) → {@(tactic auto) ok : x ∈ α} → p x
(ps ! _) {s} = lookupAll ps s

{-# INLINE _!_ #-}

opaque
  unfolding All

  mapAll : (f : ∀ {@0 x} → p x → q x) → All p α → All q α
  mapAll f List.ANil = List.ANil
  mapAll f (List.ACons p ps) = List.ACons (f p) (mapAll f ps)
  {-# COMPILE AGDA2HS mapAll #-}

  tabulateAll : Rezz _ α → (f : ∀ {@0 x} → (x ∈ α) → p x) → All p α
  tabulateAll (rezz []) f = List.ANil
  tabulateAll (rezz (x ∷ α)) f = List.ACons (f inHere) (tabulateAll (rezz-id) (f ∘ inThere))
  {-# COMPILE AGDA2HS tabulateAll #-}

  allIn : {@0 l : Scope name} → All p l → All (λ el → p el × el ∈ l) l
  allIn List.ANil = List.ANil
  allIn (List.ACons x al) = List.ACons (x , inHere) (mapAll (second inThere) (allIn al))
  {-# COMPILE AGDA2HS allIn #-}

opaque
  unfolding All
  -- for refl and lp to typecheck
  unfolding lookupAll inHere subLeft splitRefl subBindDrop subJoinDrop splitJoinRight

  allLookup : {@0 l : Scope name}
            → (ls : All p l)
            → All (λ el → ∃ (el ∈ l × p el) (λ (i , pi) → lookupAll ls i ≡ pi)) l
  allLookup List.ANil = List.ANil
  allLookup (List.ACons ph ls) =
    List.ACons ((inHere , ph) ⟨ refl ⟩)
               (mapAll (λ where
                 ((i , pi) ⟨ lp ⟩) → ((inThere i) , pi) ⟨ lp ⟩) (allLookup ls))
  {-# COMPILE AGDA2HS allLookup #-}

opaque
  unfolding All lookupAll mapAll

  AllThings : Set₁
  AllThings = Set
