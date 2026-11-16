{-# OPTIONS --cohesion --without-K --flat-split #-}

module ClosedSliceExamples where

open import Foundations
open import ClosedSliceShape
open import DeclareClosedShape
open import Agda.Builtin.Bool

bool-set : IsSet Bool
bool-set false false refl refl = refl
bool-set true true refl refl = refl

bool-discrete : Discrete Bool
bool-discrete false = (box false , refl) , λ where
  (box false , refl) → refl
bool-discrete true = (box true , refl) , λ where
  (box true , refl) → refl

unit-set : IsSet ⊤
unit-set tt tt refl refl = refl

unit-discrete : Discrete ⊤
unit-discrete tt = (box tt , refl) , λ where
  (box tt , refl) → refl

-- Closed native input spaces. Their cohesion is left unspecified.
postulate Space₀ Space₁ : Set

Family : Bool → Set
Family false = Space₀
Family true = Space₁

unquoteDecl shaped = declareClosedShape shaped
  (quoteTerm (ClosedShapeOver Bool bool-set bool-discrete Family))

-- Ordinary native dependent types in an open context, projected from the
-- generated whole-slice shape. These are not claimed to be fiberwise shapes.
ShapedFamily : Bool → Set
ShapedFamily = Output.family shaped

unit-in-context : (b : Bool) → Family b → ShapedFamily b
unit-in-context = Output.family-unit shaped

swap : Bool → Bool
swap false = true
swap true = false

ReindexedFamily : Bool → Set
ReindexedFamily b = Family (swap b)

unquoteDecl reshaped = declareClosedShape reshaped
  (quoteTerm (ClosedShapeOver Bool bool-set bool-discrete ReindexedFamily))

-- Native reindexing of the first shape and shape of the reindexed family are
-- separate constructions. No judgmental equality or equivalence is asserted.
reindex-shape : Bool → Set
reindex-shape b = Output.family shaped (swap b)

shape-reindex : Bool → Set
shape-reindex = Output.family reshaped
