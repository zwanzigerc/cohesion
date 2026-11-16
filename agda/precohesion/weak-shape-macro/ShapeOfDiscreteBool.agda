{-# OPTIONS --cohesion --without-K --flat-split #-}

-- Fidelity test for the contextual shape macro.
-- Claude (Fable), 11 November 2026; part of the Fable overlay on bundle v4.
--
-- From ONE macro-generated shape axiom, in the empty context, this derives
-- that the shape of the discrete set Bool is Bool again (Π₀Δ ≅ id at 2):
--
--   retract : r (η (end-at , raise b)) ≡ b      existence half of the UP
--   unique  : η (end-at , raise (r z)) ≡ z      uniqueness half of the UP
--
-- The bundle's own suite uses only the existence half (factor, factor-β).
-- The uniqueness half needs function extensionality, taken here as an
-- explicit crisp hypothesis, and box-crisp-path from NativeSharp.
-- The statement is at the level of the total space over the one-point
-- captured context.
--
-- ShapeChoice.agda (Astra) proves uniqueness of the reflection in general;
-- this file is the smallest concrete instance. It checks against bundles
-- v1 and v4 unchanged, and is run by check.py.
module ShapeOfDiscreteBool where

open import Foundations
open import Agda.Builtin.Bool
import CapturedShape as C
open C using (CapturedShape)
open import CaptureShape using (shape)
open import CaptureContext
import RelativeSliceShape as R
open import PullbackSetFibers using (retract-set; left-inverse)
open import ClosedSliceExamples using (bool-set; bool-discrete)
open import NativeSharp using (box-crisp-path)

-- The macro's output: one postulate, generated here.
s : CapturedShape Bool
s = shape

Ctx : Set
Ctx = C.Output.context s

Fam : Ctx → Set
Fam = C.Output.family s

K : R.RelativeShapeOver Ctx (C.Output.context-discrete s) Fam
K = C.Output.whole-context s

S : Set
S = R.Output.Total K

p : S → Ctx
p = R.Output.projection K

η : Σ Ctx Fam → S
η = R.Output.unit K

η-over : (a : Σ Ctx Fam) → p (η a) ≡ fst a
η-over = R.Output.unit-over K

-- The captured empty context is a one-point type, hence a set.
ctx-prop : IsProp Ctx
ctx-prop end-at end-at = refl

prop-set : ∀ {a} {A : Set a} → IsProp A → IsSet A
prop-set {A = A} h x y u v = lemma u ∙ sym (lemma v)
  where
  lemma : {z : A} (w : x ≡ z) → w ≡ sym (h x x) ∙ h x z
  lemma refl = sym (left-inverse (h x x))

ctx-set : IsSet Ctx
ctx-set = prop-set ctx-prop

-- Bool as an admissible target over the context.
qB : Bool → Ctx
qB _ = end-at

qB-set-fibers : R.SetFibers qB
qB-set-fibers γ = retract-set fst (λ b → b , ctx-prop end-at γ)
  (λ { (b , e) → ap (λ e' → b , e') (ctx-set end-at γ (ctx-prop end-at γ) e) })
  bool-set

f-fun : Σ Ctx Fam → Bool
f-fun (end-at , raise b) = b

f-tri : (a : Σ Ctx Fam) → qB (f-fun a) ≡ fst a
f-tri (end-at , raise b) = refl

f-over : R.MapOver (fst {B = Fam}) qB
f-over = R.over-map f-fun f-tri

-- EXISTENCE half of the universal property.
r-over : R.MapOver p qB
r-over = R.Output.factor K Bool bool-discrete qB qB-set-fibers f-over

r : S → Bool
r = R.function r-over

r-η : (a : Σ Ctx Fam) → r (η a) ≡ f-fun a
r-η = R.Output.factor-on-unit K Bool bool-discrete qB qB-set-fibers f-over

-- Bool is a retract of its shape.
retract : (b : Bool) → r (η (end-at , raise b)) ≡ b
retract b = r-η (end-at , raise b)

-- UNIQUENESS half.
module WithFunExt (@♭ fe : FunExt) where

  back : S → S
  back z = η (end-at , raise (r z))

  g-over : R.MapOver p p
  g-over = R.over-map back (λ z → ctx-prop (p (back z)) (p z))

  id-over : R.MapOver p p
  id-over = R.over-map (λ z → z) (λ z → refl)

  pre : R.MapOver p p → R.MapOver (fst {B = Fam}) p
  pre = R.precomposeOver Ctx Fam S p η η-over S p

  over-map-eq : {X : Set} {pX : X → Ctx} {f1 f2 : X → S}
              → (F : f1 ≡ f2)
              → {t1 : (x : X) → p (f1 x) ≡ pX x}
              → {t2 : (x : X) → p (f2 x) ≡ pX x}
              → R.over-map {p = pX} {q = p} f1 t1 ≡ R.over-map f2 t2
  over-map-eq refl {t1} {t2} =
    ap (R.over-map _) (fe (λ x → ctx-set _ _ (t1 x) (t2 x)))

  agree : (a : Σ Ctx Fam) → back (η a) ≡ η a
  agree (end-at , raise b) =
    ap (λ b' → η (end-at , raise b')) (r-η (end-at , raise b))

  e : pre g-over ≡ pre id-over
  e = over-map-eq (fe agree)

  E : IsEquiv (flat-map pre)
  E = R.Output.universal K S (R.Output.total-discrete K) p (R.Output.family-set K)

  boxed : box g-over ≡ box id-over
  boxed = sym (retraction E (box g-over))
        ∙ ap (inverse E) (box-crisp-path e)
        ∙ retraction E (box id-over)

  -- The other inverse law: the shape of Bool is Bool.
  unique : (z : S) → η (end-at , raise (r z)) ≡ z
  unique z = ap (λ m → R.function m z) (ap counit boxed)
