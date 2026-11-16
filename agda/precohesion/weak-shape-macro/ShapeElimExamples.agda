{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Uses of shape-elim. Added 11 November 2026 (Fable); see FABLE-ADDITIONS.txt.
module ShapeElimExamples where

open import Foundations
open import Agda.Builtin.Bool
import CapturedShape as C
open C using (CapturedShape)
open import CaptureShape using (shape)
open import DeclareCapturedShape using (declareShape)
open import ShapeElim
open import ClosedSliceExamples using (bool-set; bool-discrete)

-- 1. Empty context: a map out of a closed space into Bool.
postulate
  X Y : Set
  colour : X → Bool
  g : X → Y

sX : CapturedShape X
sX = shape

sY : CapturedShape Y
sY = shape

colour-elim : ShapeElim sX colour
colour-elim = shape-elim bool-set bool-discrete

ʃ-colour : C.Output.carrier sX → Bool
ʃ-colour = ShapeElim.map colour-elim

ʃ-colour-unit : (x : X) → ʃ-colour (C.Output.unit sX x) ≡ colour x
ʃ-colour-unit = ShapeElim.map-unit colour-elim

-- 2. The target is another shape: the action of shape on a map.
map-elim : ShapeElim sX (λ x → C.Output.unit sY (g x))
map-elim = shape-elim (C.Output.carrier-set sY) (carrier-discrete sY)

ʃ-map : C.Output.carrier sX → C.Output.carrier sY
ʃ-map = ShapeElim.map map-elim

ʃ-map-unit : (x : X) → ʃ-map (C.Output.unit sX x) ≡ C.Output.unit sY (g x)
ʃ-map-unit = ShapeElim.map-unit map-elim

-- 3. An open crisp context, module style. Target and map are variables of
--    the context in which the shape is formed.
module Open (@♭ A D : Set) (@♭ D-set : IsSet D) (@♭ D-discrete : Discrete D)
            (@♭ f : A → D) where
  s : CapturedShape A
  s = shape

  e : ShapeElim s f
  e = shape-elim D-set D-discrete

  rec : C.Output.carrier s → D
  rec = ShapeElim.map e

  rec-unit : (a : A) → rec (C.Output.unit s a) ≡ f a
  rec-unit = ShapeElim.map-unit e

-- 4. An open crisp context, module style, where the target is another shape
--    formed in the same module: functoriality in context.
module Functor (@♭ A B : Set) (@♭ h : A → B) where
  sA : CapturedShape A
  sA = shape

  sB : CapturedShape B
  sB = shape

  e : ShapeElim sA (λ a → C.Output.unit sB (h a))
  e = shape-elim (C.Output.carrier-set sB) (carrier-discrete sB)

  ʃh : C.Output.carrier sA → C.Output.carrier sB
  ʃh = ShapeElim.map e

  ʃh-unit : (a : A) → ʃh (C.Output.unit sA a) ≡ C.Output.unit sB (h a)
  ʃh-unit = ShapeElim.map-unit e

-- 5. The same in function style.
SA : (@♭ A B : Set) (@♭ h : A → B) → CapturedShape {ℓ = lsuc lzero} A
SA A B h = shape

SB : (@♭ A B : Set) (@♭ h : A → B) → CapturedShape {ℓ = lsuc lzero} B
SB A B h = shape

functor : (@♭ A B : Set) (@♭ h : A → B)
        → ShapeElim (SA A B h) (λ a → C.Output.unit (SB A B h) (h a))
functor A B h = shape-elim (C.Output.carrier-set (SB A B h)) (carrier-discrete (SB A B h))

-- 6. Shapes made by the declaration frontend, and a target given by a later
--    plain call that reuses the registered choice: the action of shape on
--    an endomorphism.
module Declared (@♭ A : Set) (@♭ t : A → A) where
  unquoteDecl s = declareShape s A

  again : CapturedShape A
  again = shape

  e : ShapeElim s (λ a → C.Output.unit again (t a))
  e = shape-elim (C.Output.carrier-set again) (carrier-discrete again)

  ʃt : C.Output.carrier s → C.Output.carrier s
  ʃt = ShapeElim.map e

  ʃt-unit : (a : A) → ʃt (C.Output.unit s a) ≡ C.Output.unit s (t a)
  ʃt-unit = ShapeElim.map-unit e
