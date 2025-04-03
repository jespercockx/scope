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
  @0 rα rβ  : RScope name
  @0 x y  : name
  p q     : @0 name → Set

opaque
  unfolding Scope

  {- All p α is a proof that  ∀ (x ∈ α), p x -}
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
  allJoin {p = p} pas List.ANil = pas
  allJoin {p = p} pas (List.ACons px pbs) = List.ACons px (allJoin pas pbs)
  {-# COMPILE AGDA2HS allJoin #-}

opaque
  unfolding RScope

  {- All p α is a proof that  ∀ (x ∈ rα), p x -}
  AllR : (p : @0 name → Set) → @0 RScope name → Set
  AllR p = List.All λ x → p (get x)
  {-# COMPILE AGDA2HS AllR #-}

  allEmptyR : AllR p mempty
  allEmptyR = List.ANil
  {-# COMPILE AGDA2HS allEmptyR #-}

  allSinglR : p x → AllR p (x ◂)
  allSinglR p = List.ACons p List.ANil
  {-# COMPILE AGDA2HS allSinglR #-}

  getAllSinglR : AllR p (x ◂) → p x
  getAllSinglR (List.ACons p List.ANil) = p
  {-# COMPILE AGDA2HS getAllSinglR #-}

  allJoinR : AllR p rα → AllR p rβ → AllR p (rβ <> rα)
  allJoinR {p = p} pas List.ANil = pas
  allJoinR {p = p} pas (List.ACons px pbs) = List.ACons px (allJoinR pas pbs)
  {-# COMPILE AGDA2HS allJoinR #-}

opaque
  unfolding All

  lookupAll : All p α → x ∈ α → p x
  lookupAll (List.ACons pz pzs) (Zero  ⟨ IsZero  refl ⟩) = pz
  lookupAll (List.ACons _ pzs) (Suc n ⟨ IsSuc pn ⟩) = lookupAll pzs (n ⟨ pn ⟩)
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
  unfolding AllR

  lookupAllR : AllR p rα → rα ∋ x → p x
  lookupAllR (List.ACons pz pzs) (Zero  ⟨ IsZeroR  refl ⟩) = pz
  lookupAllR (List.ACons _ pzs) (Suc n ⟨ IsSucR pn ⟩) = lookupAllR pzs (n ⟨ pn ⟩)
  {-# COMPILE AGDA2HS lookupAllR #-}

  findAllR : {q : Set}
          → AllR p rα
          → ({@0 el : name} → (pel : p el) → (ela : rα ∋ el) → Maybe q)
          → Maybe q
  findAllR List.ANil qc = Nothing
  findAllR (List.ACons px al) qc =
    case qc px (inRHere) of λ where
      (Just qt) → Just qt
      Nothing → findAllR al (λ pel i → qc pel (inRThere i))
  {-# COMPILE AGDA2HS findAllR #-}

opaque
  unfolding All Sub Split lookupAll inHere splitRefl

  lookupHere : (l : All p α) (ph : p x)
             → lookupAll (allJoin l (allSingl ph)) inHere ≡ ph
  lookupHere _ _ = refl

opaque
  unfolding All Sub Split lookupAll inThere subBindDrop subJoinDrop splitJoinRight

  lookupThere : {ph : p y} {pi : p x} {l : All p α} {i : x ∈ α}
              → lookupAll l i ≡ pi
              → lookupAll (allJoin l (allSingl ph)) (inThere i) ≡ pi
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
      (λ where {{refl}} → Just (Erased (cong (λ t → t ▸ (get x)) (get rt))))
      Nothing
  {-# COMPILE AGDA2HS allInScope #-}

opaque
  unfolding AllR

  mapAllR : (f : ∀ {@0 x} → p x → q x) → AllR p rα → AllR q rα
  mapAllR f List.ANil = List.ANil
  mapAllR f (List.ACons p ps) = List.ACons (f p) (mapAllR f ps)
  {-# COMPILE AGDA2HS mapAllR #-}

  tabulateAllR : Rezz rα → (f : ∀ {@0 x} → (rα ∋ x) → p x) → AllR p rα
  tabulateAllR (rezz []) f = List.ANil
  tabulateAllR (rezz (x ∷ α)) f = List.ACons (f inRHere) (tabulateAllR (rezz-id) (f ∘ inRThere))
  {-# COMPILE AGDA2HS tabulateAllR #-}

  allInR : AllR p rα → AllR (λ el → p el × rα ∋ el) rα
  allInR List.ANil = List.ANil
  allInR (List.ACons x al) = List.ACons (x , inRHere) (mapAllR (second inRThere) (allInR al))
  {-# COMPILE AGDA2HS allInR #-}

  rezzAllR : AllR p rα → Rezz rα
  rezzAllR List.ANil = rezz []
  rezzAllR (List.ACons {x = x} _ xs) = rezzCong2 (_∷_) rezzErase (rezzAllR xs)
  {-# COMPILE AGDA2HS rezzAllR #-}

  allInRScope : ∀ {@0 γ}
               (als : AllR (λ c → c ∈ γ) rα)
               (bls : AllR (λ c → c ∈ γ) rβ)
             → Maybe (Erase (rα ≡ rβ))
  allInRScope List.ANil                  List.ANil = Just (Erased refl)
  allInRScope List.ANil                  (List.ACons _ _) = Nothing
  allInRScope (List.ACons         _ _)   List.ANil = Nothing
  allInRScope (List.ACons {x = x} p als) (List.ACons q bls) = do
    rt ← allInRScope als bls
    ifDec (decIn p q)
      (λ where {{refl}} → Just (Erased (cong (λ t → (get x) ◂ t) (get rt))))
      Nothing
  {-# COMPILE AGDA2HS allInRScope #-}

opaque
  unfolding All lookupAll

  allLookup : (ls : All p α)
            → All (λ el → ∃ (el ∈ α × p el) (λ (i , pri) → lookupAll ls i ≡ pri)) α
  allLookup List.ANil = List.ANil
  allLookup (List.ACons ph ls) =
    List.ACons
      ((inHere , ph) ⟨ lookupHere ls ph ⟩)
      (mapAll (λ where ((i , pri) ⟨ lp ⟩) → ((inThere i) , pri) ⟨ lookupThere lp ⟩)
              (allLookup ls))
  {-# COMPILE AGDA2HS allLookup #-}

opaque
  unfolding All findAll lookupAll lookupHere lookupThere
  unfolding mapAll tabulateAll allIn rezzAll allInScope allLookup
  unfolding AllR mapAllR

  AllThings : Set₁
  AllThings = Set
