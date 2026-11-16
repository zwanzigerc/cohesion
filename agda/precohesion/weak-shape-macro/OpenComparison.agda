{-# OPTIONS --cohesion --without-K --flat-split #-}

-- SET-SOURCE STAGE O2: where points-to-pieces of both totals is invertible,
-- so is the canonical comparison. Opus, 14 November 2026;
-- opus-closed-limits-01 (delta 03), implementing FABLE-PLAN-SET-SOURCE-01
-- §4.2 (OPEN-QUALITY-AND-COMPARISON-NATIVE-ROUTE-01, part 2).
--
-- Generic (plan §2): crisp level i, discrete bases B B′ with B a SET, a
-- family A, f : B′ → B, payloads K, K′, fe : FunExtAt i (for TotalData).
-- sX, sY are TotalData.total-data of K, K′ (carrier and unit those of the
-- payloads), exactly as in the kernel; D = ReindexingAssembly.TotalForm.
--
--   core : IsEquiv θX → IsEquiv θY → IsEquiv D.comparison-total
--   o2   : (P → IsEquiv θX) → (P → IsEquiv θY) → P → IsEquiv D.comparison-total
--          for ANY type P (the support enters only as a hypothesis).
--
-- Steps (plan §4.2). D♭ = Pullback (fst ∘ counit) f is discrete
-- (DiscretePullback.pullback-discrete); L : ♭ Y → D♭,
-- box (b′ , a) ↦ (b′ , box (f b′ , a) , refl), is an equivalence with no
-- hypothesis, its inverse being the inverse counit of D♭ followed by a
-- crisp match and transport in A (a crisp refl-match is refused by the
-- compiler; the crisp pair path is boxed by box-crisp-path instead). H : D♭ → PulledTotal, (b′ , v , e) ↦ (b′ , θX v , uo ∙ e), is
-- an equivalence when θX is (B a set). comparison-total ∘ θY ∼ H ∘ L by
-- Output.factor-on-unit of K′ at the pulled unit. Cancel θY.
-- Nothing is postulated; no shape is formed; no extensionality beyond the
-- fe that TotalData asks for.
module OpenComparison where

open import Foundations
open import Adjointify using (quasi-inverse)
open import RelativeSliceShape
open import FlatContext using (flat-discrete)
open import NativeSharp using (transport; box-crisp-path)
open import DiscretePullback using (Pullback; pullback-discrete)
open import ShapeChoice using (FunExtAt)
open import GlobalPrecohesion using (ShapeData; points-to-pieces)
open import ReindexingAssembly using (module TotalForm)
open import TotalBridge using (module TotalData)
open import ClosedLimits using (pb-path; equiv-compose)
open import SetSourceReflection using (equiv-homotopy)

-- The inverse of an equivalence is one.
inverse-equiv : ∀ {a b} {A : Set a} {B : Set b} {h : A → B}
              → (e : IsEquiv h) → IsEquiv (inverse e)
inverse-equiv {h = h} e =
  quasi-inverse {f = inverse e} h (retraction e) (section e)

module O2 {@♭ i : Level} (@♭ fe : FunExtAt i)
  (@♭ B B′ : Set i) (@♭ dB : Discrete B) (@♭ dB′ : Discrete B′)
  (@♭ B-set : IsSet B) (@♭ B′-set : IsSet B′)
  (@♭ A : B → Set i) (@♭ f : B′ → B)
  (@♭ K : RelativeShapeOver B dB A)
  (@♭ K′ : RelativeShapeOver B′ dB′ (A ∘ f)) where

  module D = TotalForm B B′ dB dB′ A f K K′

  X : Set i
  X = Σ B A

  Y : Set i
  Y = Σ B′ (A ∘ f)

  sX : ShapeData X
  sX = TotalData.total-data fe B-set K

  sY : ShapeData Y
  sY = TotalData.total-data fe B′-set K′

  θX : ♭ X → Output.Total K
  θX = points-to-pieces sX

  θY : ♭ Y → Output.Total K′
  θY = points-to-pieces sY

  -- 1. The flat pullback and L.
  base♭ : ♭ X → B
  base♭ v = fst (counit v)

  D♭ : Set i
  D♭ = Pullback base♭ f

  dD♭ : Discrete D♭
  dD♭ = pullback-discrete dB dB′ (flat-discrete X) base♭ f

  L : ♭ Y → D♭
  L (box (b′ , a)) = b′ , box (f b′ , a) , refl

  back : ♭ D♭ → ♭ Y
  back (box (b′ , box (b , a) , e)) = box (b′ , transport A e a)

  -- A pair path along a base path (ordinary J).
  lift-path : {b c : B} (a : A b) (e : b ≡ c)
            → _≡_ {A = X} (b , a) (c , transport A e a)
  lift-path a refl = refl

  -- At crisp data the pair path is crisp and is boxed (box-crisp-path);
  -- the pullback coordinate is then settled by sethood of B.
  L-back : (c : ♭ D♭) → L (back c) ≡ counit c
  L-back (box (b′ , box (b , a) , e)) =
    pb-path B-set refl (sym (box-crisp-path (lift-path a e)))

  L-equiv : IsEquiv L
  L-equiv = quasi-inverse {f = L} (λ d → back (inverse dD♭ d))
    (λ d → L-back (inverse dD♭ d) ∙ section dD♭ d)
    (λ { (box (b′ , a)) → ap back (retraction dD♭ (box (b′ , box (f b′ , a) , refl))) })

  -- 2. H, an equivalence when θX is.
  H : D♭ → D.PulledTotal
  H (b′ , v , e) = b′ , θX v , (Output.unit-over K (counit v) ∙ e)

  H-equiv : IsEquiv θX → IsEquiv H
  H-equiv eX = quasi-inverse {f = H} H⁻¹
    (λ { (b′ , s , q) → pb-path B-set refl (section eX s) })
    (λ { (b′ , v , e) → pb-path B-set refl (retraction eX v) })
    where
    H⁻¹ : D.PulledTotal → D♭
    H⁻¹ (b′ , s , q) = b′ , inverse eX s ,
      (sym (Output.unit-over K (counit (inverse eX s)))
       ∙ ap (Output.projection K) (section eX s) ∙ q)

  -- 3. The square: comparison-total ∘ θY ∼ H ∘ L.
  square : (w : ♭ Y) → D.comparison-total (θY w) ≡ H (L w)
  square (box (b′ , a)) =
    Output.factor-on-unit K′ D.PulledTotal D.pulled-discrete
      D.pulled-projection D.pulled-set-fibers D.pulled-unit (b′ , a)
    ∙ pb-path B-set refl refl

  -- 4. Cancel θY.
  core : IsEquiv θX → IsEquiv θY → IsEquiv D.comparison-total
  core eX eY = equiv-homotopy pointwise
    (equiv-compose (inverse-equiv eY) (equiv-compose L-equiv (H-equiv eX)))
    where
    pointwise : (z : Output.Total K′)
              → H (L (inverse eY z)) ≡ D.comparison-total z
    pointwise z = sym (square (inverse eY z)) ∙ ap D.comparison-total (section eY z)

  o2 : {P : Set (lsuc i)} → (P → IsEquiv θX) → (P → IsEquiv θY)
     → P → IsEquiv D.comparison-total
  o2 oX oY p = core (oX p) (oY p)
