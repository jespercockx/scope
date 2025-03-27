module Scope where

open import Scope.Core  public
open import Scope.Reverse
open import Scope.Split public
open import Scope.Sub   public
open import Scope.In    public
open import Scope.Cut   public
open import Scope.Diff  public
open import Scope.Renaming public
open import Scope.All   public

opaque
  unfolding ScopeCoreThings ReverseThings SplitThings SubThings InThings DiffThings AllThings

  ScopeThings : Set₁
  ScopeThings = Set
