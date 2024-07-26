module Scope.All where

open import Haskell.Prelude hiding (All)
open import Haskell.Extra.Dec
open import Haskell.Extra.Erase
open import Haskell.Extra.Refinement
open import Haskell.Law.Equality
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
  @0 x y  : name
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

opaque
  unfolding All Sub Split lookupAll inHere splitRefl

  lookupHere : (l : All p α) (ph : p x)
             → lookupAll (allJoin (allSingl ph) l) inHere ≡ ph
  lookupHere _ _ = refl

opaque
  unfolding All Sub Split lookupAll inThere subBindDrop subJoinDrop splitJoinRight

  lookupThere : {ph : p y} {pi : p x} {l : All p α} {i : x ∈ α}
              → lookupAll l i ≡ pi
              → lookupAll (allJoin (allSingl ph) l) (inThere i) ≡ pi
  lookupThere p = p

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

  tabulateAll : Rezz α → (f : ∀ {@0 x} → (x ∈ α) → p x) → All p α
  tabulateAll (rezz []) f = List.ANil
  tabulateAll (rezz (x ∷ α)) f = List.ACons (f inHere) (tabulateAll (rezz-id) (f ∘ inThere))
  {-# COMPILE AGDA2HS tabulateAll #-}

  allIn : All p α → All (λ el → p el × el ∈ α) α
  allIn List.ANil = List.ANil
  allIn (List.ACons x al) = List.ACons (x , inHere) (mapAll (second inThere) (allIn al))
  {-# COMPILE AGDA2HS allIn #-}

  rezzAll : All p α → Rezz α
  rezzAll List.ANil = rezz []
  rezzAll (List.ACons {x = x} _ xs) = rezzCong2 (_∷_) rezzErase (rezzAll xs)
  {-# COMPILE AGDA2HS rezzAll #-}

  allInScope : ∀ {@0 γ}
               (als : All (λ c → c ∈ γ) α)
               (bls : All (λ c → c ∈ γ) β)
             → Maybe (Erase (α ≡ β))
  allInScope List.ANil                  List.ANil = Just (Erased refl)
  allInScope List.ANil                  (List.ACons _ _) = Nothing
  allInScope (List.ACons         _ _)   List.ANil = Nothing
  allInScope (List.ACons {x = x} p als) (List.ACons q bls) = do
    rt ← allInScope als bls
    ifDec (decIn p q)
      (λ where {{refl}} → Just (Erased (cong (λ t → bind (get x) t) (get rt))))
      Nothing
  {-# COMPILE AGDA2HS allInScope #-}

opaque
  unfolding All lookupAll

  allLookup : (ls : All p α)
            → All (λ el → ∃ (el ∈ α × p el) (λ (i , pi) → lookupAll ls i ≡ pi)) α
  allLookup List.ANil = List.ANil
  allLookup (List.ACons ph ls) =
    List.ACons
      ((inHere , ph) ⟨ lookupHere ls ph ⟩)
      (mapAll (λ where ((i , pi) ⟨ lp ⟩) → ((inThere i) , pi) ⟨ lookupThere lp ⟩)
              (allLookup ls))
  {-# COMPILE AGDA2HS allLookup #-}

opaque
  unfolding All findAll lookupAll lookupHere lookupThere
  unfolding mapAll tabulateAll allIn rezzAll allInScope allLookup

  AllThings : Set₁
  AllThings = Set
