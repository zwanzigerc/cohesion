{-# OPTIONS --cohesion --without-K --flat-split #-}

-- SET-SOURCE STAGE B: the canonical comparison of a closed diagram with
-- equality decidable up to P on both bases is an equivalence on every
-- fibre. Opus, 14 November 2026; opus-closed-limits-01 (delta 06),
-- implementing FABLE-PLAN-SET-SOURCE-01 §8 (CLOSED-BOOLEAN-BC-NATIVE-
-- ROUTE-01, sections 1–2) against Fable's UNCHANGED
-- SetSourceKernelStatements.ClosedComparison (exact telescope; arbitrary
-- input fibres, closed total, discrete closed set bases).
--
--   Proof.statement-B : Statement-B
--
-- Steps (plan §8.2).
--  1. Output.Total is closed (discrete-elim on P; at a crisp point of P the
--     constant map at the unit of the centre and the identity agree on
--     units: uniqueness of TotalData.total-data), so each fibre is closed;
--     the total of A ∘ g is closed (a proposition with a point under P).
--  2. For crisp γ₀ and a crisp CLOSED discrete set D, D̂ γ = (γ ≡ γ₀) → D
--     has a discrete total with set fibres: at crisp γ the crisp decision
--     δ γ γ₀ is eliminated by CrispTruncation.crisp-trunc-rec into the
--     proposition Discrete (D̂ γ); a crisp path makes D̂ γ a retract of D,
--     a crisp (γ ≡ γ₀) → P makes it contractible since D is closed
--     (RetractDiscrete both times). Set fibres: fun-set below.
--  3. The restricted recursor rec₀ (factor through the payload, evaluate
--     at the triangle) with rec₀-η, and uniqueness unique₀ for crisp maps
--     with crisp agreement on units (the universal field, boxed).
--  4. At crisp γ′, the comparison has the inverse rec₀ for K at g γ′ into
--     the closed fibre of K′ at γ′; both composites are identities by the
--     two uniquenesses and comparison-on-unit; GlobalChoice.set-equiv.
--  5. DiscretePullback.discrete-ind for an ordinary γ′.
-- Hypotheses: those of the telescope only (fe, T, P, dP, sets, closedness,
-- the two crisp decisions). No continuity, product or Nullstellensatz. No
-- sethood of the fibres of A. Nothing is postulated.
module ClosedComparisonProof where

open import Foundations
open import RelativeSliceShape
open import CaptureContext using (CrispUnitAt; end-at; unit-at-discrete)
open import NativeSharp using (transport; box-crisp-path)
open import DiscretePullback using (discrete-ind)
open import PullbackSetFibers using (fiber-fst-set)
open import ShapeElim using (module SigmaDiscrete; module FiberDiscrete)
open import RetractDiscrete using (retract-discrete)
open import SmallPropositions using (retract-is-prop; subtype-path)
open import GlobalPrecohesion using (unique; discrete-elim)
open import GlobalPropositions using (FunExt₂; equiv-is-prop)
open import GlobalChoice using (set-equiv)
open import TruncationDiscrete using (_⊎_; inl; inr)
open import OrdinaryTruncation using (PropTruncation)
open import CrispTruncation using (crisp-trunc-rec)
open import ClosedReflection using (Closed)
open import TotalBridge using (module TotalData)
open import ReindexingAssembly using (module TotalForm)
open import SetSourceKernelStatements using (module ClosedComparison)

------------------------------------------------------------------------
-- Function types into sets are sets, from plain FE (the corrected
-- extensionality fe′ H = fe H ∙ sym (fe (λ _ → refl)) is a retraction of
-- happly; the pointwise type is a proposition).

private
  cancel-r : ∀ {a} {X : Set a} {x y : X} (q : x ≡ y) → q ∙ sym q ≡ refl
  cancel-r refl = refl

fun-set : ∀ {a b} → FunExt₂ a b → {X : Set a} {D : Set b}
        → IsSet D → IsSet (X → D)
fun-set fe {X} {D} D-set f g =
  retract-is-prop (λ q → happly q) fe′ back pointwise-prop
  where
  fe′ : {h k : X → D} → ((x : X) → h x ≡ k x) → h ≡ k
  fe′ {k = k} H = fe H ∙ sym (fe {f = k} {g = k} (λ _ → refl))

  back : {h k : X → D} (q : h ≡ k) → fe′ (happly q) ≡ q
  back {h} refl = cancel-r (fe {f = h} {g = h} (λ _ → refl))

  pointwise-prop : IsProp ((x : X) → f x ≡ g x)
  pointwise-prop H H′ = fe (λ x → D-set (f x) (g x) (H x) (H′ x))

-- A pair path over a set base with a trivial base component.
private
  fibre-of-pair : ∀ {a b} {X : Set a} {F : X → Set b} → IsSet X
                → {x : X} {s t : F x} → _≡_ {A = Σ X F} (x , s) (x , t) → s ≡ t
  fibre-of-pair {F = F} X-set {x} {s} {t} r =
    ap (λ q → transport F q s) (X-set _ _ refl (ap fst r)) ∙ lemma r
    where
    lemma : {w : Σ _ F} (r : (x , s) ≡ w) → transport F (ap fst r) s ≡ snd w
    lemma refl = refl

------------------------------------------------------------------------

module Proof {@♭ ℓ : Level}
  (@♭ fe : FunExt₂ ℓ ℓ) (@♭ T : PropTruncation ℓ)
  (@♭ P : Set ℓ) (@♭ P-prop : IsProp P) (@♭ dP : Discrete P)
  (@♭ Γ Γ′ : Set ℓ) (@♭ dΓ : Discrete Γ) (@♭ dΓ′ : Discrete Γ′)
  (@♭ Γ-set : IsSet Γ) (@♭ Γ′-set : IsSet Γ′)
  (@♭ closed-Γ : Closed P Γ) (@♭ closed-Γ′ : Closed P Γ′)
  (@♭ A : Γ → Set ℓ) (@♭ closed-total : Closed P (Σ Γ A))
  (@♭ g : Γ′ → Γ)
  (@♭ K : RelativeShapeOver Γ dΓ A)
  (@♭ K′ : RelativeShapeOver Γ′ dΓ′ (A ∘ g)) where

  open ClosedComparison fe T P P-prop dP Γ Γ′ dΓ dΓ′ Γ-set Γ′-set
    closed-Γ closed-Γ′ A closed-total g K K′
    using (Decision; module C; Statement-B)
  open PropTruncation T using (∥_∥)

  contr-prop : ∀ {X : Set ℓ} → IsContr X → IsProp X
  contr-prop (c , h) x y = sym (h x) ∙ h y

  -- 1′. The total of A ∘ g is closed.
  closed-total′ : Closed P (Σ Γ′ (A ∘ g))
  closed-total′ p = point , λ w → total-prop point w
    where
    cA = closed-total p
    γ′₀ = fst (closed-Γ′ p)

    to-base : fst (fst cA) ≡ g γ′₀
    to-base = contr-prop (closed-Γ p) _ _

    point : Σ Γ′ (A ∘ g)
    point = γ′₀ , transport A to-base (snd (fst cA))

    total-prop : IsProp (Σ Γ′ (A ∘ g))
    total-prop (γ , a) (γ₁ , b) = helper (contr-prop (closed-Γ′ p) γ γ₁) a b
      where
      helper : {γ γ₁ : Γ′} (q : γ ≡ γ₁) (a : A (g γ)) (b : A (g γ₁))
             → _≡_ {A = Σ Γ′ (A ∘ g)} (γ , a) (γ₁ , b)
      helper {γ} refl a b = ap (λ t → γ , t)
        (fibre-of-pair Γ-set (contr-prop cA (g γ , a) (g γ , b)))

  -- 1–3, for one crisp payload over a crisp closed discrete set base.
  module OverBase {@♭ Δ : Set ℓ} {@♭ dΔ : Discrete Δ} (@♭ Δ-set : IsSet Δ)
    (@♭ closed-Δ : Closed P Δ)
    {@♭ F : Δ → Set ℓ} (@♭ closed-ΣF : Closed P (Σ Δ F))
    (@♭ L : RelativeShapeOver Δ dΔ F) (@♭ δΔ : Decision Δ) where

    Tot : Set ℓ
    Tot = Output.Total L

    p : Tot → Δ
    p = Output.projection L

    u : Σ Δ F → Tot
    u = Output.unit L

    uo : (a : Σ Δ F) → p (u a) ≡ fst a
    uo = Output.unit-over L

    private
      td = TotalData.total-data fe Δ-set L
      Tot-set = TotalData.T-set fe Δ-set L

    total-closed : Closed P Tot
    total-closed = discrete-elim dP (λ _ → IsContr Tot) at-point
      where
      at-point : (@♭ q : P) → IsContr Tot
      at-point q = u (fst (closed-ΣF q)) ,
        unique td Tot Tot-set (Output.total-discrete L)
          (λ _ → u (fst (closed-ΣF q))) (λ z → z)
          (λ x → ap u (snd (closed-ΣF q) x))

    family-closed : (γ : Δ) → Closed P (Output.family L γ)
    family-closed γ q = inhabitant , fib-prop inhabitant
      where
      fib-prop : IsProp (Output.family L γ)
      fib-prop (z , e) (z′ , e′) =
        subtype-path (λ z₀ → Δ-set (p z₀) γ) (contr-prop (total-closed q) z z′)

      inhabitant : Output.family L γ
      inhabitant = fst (total-closed q) , contr-prop (closed-Δ q) _ _

    module Fib (@♭ γ₀ : Δ) where

      S₀ : Set ℓ
      S₀ = Output.family L γ₀

      η₀ : F γ₀ → S₀
      η₀ = Output.family-unit L γ₀

      module Target (@♭ D : Set ℓ) (@♭ D-set : IsSet D)
        (@♭ D-discrete : Discrete D) (@♭ D-closed : Closed P D) where

        D̂ : Δ → Set ℓ
        D̂ γ = γ ≡ γ₀ → D

        D̂-set : (γ : Δ) → IsSet (D̂ γ)
        D̂-set γ = fun-set fe D-set

        D̂-discrete : (@♭ γ : Δ) → Discrete (D̂ γ)
        D̂-discrete γ =
          crisp-trunc-rec fe T (equiv-is-prop fe counit) handler (δΔ γ γ₀)
          where
          handler : (@♭ a : (γ ≡ γ₀) ⊎ ((γ ≡ γ₀) → P)) → Discrete (D̂ γ)
          handler (inl e₀) = retract-discrete (λ φ → φ e₀) (λ d _ → d)
            (λ φ → fe (λ e → ap φ (Δ-set _ _ e₀ e))) D-discrete
          handler (inr n) = retract-discrete (λ _ → end-at {ℓ})
            (λ _ e → fst (D-closed (n e)))
            (λ φ → fe (λ e → snd (D-closed (n e)) (φ e))) unit-at-discrete

        E : Set ℓ
        E = Σ Δ D̂

        E-discrete : Discrete E
        E-discrete = SigmaDiscrete.discrete dΔ D̂-discrete

        E-set-fibers : SetFibers (fst {B = D̂})
        E-set-fibers γ = fiber-fst-set γ (D̂-set γ)

        over : (F γ₀ → D) → MapOver (fst {B = F}) (fst {B = D̂})
        over g₀ = over-map (λ x → fst x , λ e → g₀ (transport F e (snd x)))
          (λ _ → refl)

        factored : (@♭ g₀ : F γ₀ → D) → MapOver p (fst {B = D̂})
        factored g₀ = Output.factor L E E-discrete fst E-set-fibers (over g₀)

        rec₀ : (@♭ g₀ : F γ₀ → D) → S₀ → D
        rec₀ g₀ z = snd (function (factored g₀) (fst z))
          (triangle (factored g₀) (fst z) ∙ snd z)

        out-path : {w w′ : E} (r : w ≡ w′) (e : fst w ≡ γ₀) (e′ : fst w′ ≡ γ₀)
                 → snd w e ≡ snd w′ e′
        out-path {w} refl e e′ = ap (snd w) (Δ-set _ _ e e′)

        rec₀-η : (@♭ g₀ : F γ₀ → D) (a : F γ₀) → rec₀ g₀ (η₀ a) ≡ g₀ a
        rec₀-η g₀ a = out-path
          (Output.factor-on-unit L E E-discrete fst E-set-fibers (over g₀) (γ₀ , a))
          _ refl

        -- Uniqueness.
        private
          lift : (S₀ → D) → MapOver p (fst {B = D̂})
          lift h = over-map (λ z → p z , λ e → h (z , e)) (λ _ → refl)

          pre : MapOver p (fst {B = D̂}) → MapOver (fst {B = F}) (fst {B = D̂})
          pre = precomposeOver Δ F Tot p u uo E fst

          U = Output.universal L E E-discrete fst E-set-fibers

          at-γ₀ : (h h′ : S₀ → D) → ((a : F γ₀) → h (η₀ a) ≡ h′ (η₀ a))
                → (γ : Δ) → γ ≡ γ₀ → (x : F γ) (e₁ : p (u (γ , x)) ≡ γ₀)
                → h (u (γ , x) , e₁) ≡ h′ (u (γ , x) , e₁)
          at-γ₀ h h′ H .γ₀ refl x e₁ =
            ap h same-point ∙ H x ∙ sym (ap h′ same-point)
            where
            same-point : _≡_ {A = S₀} (u (γ₀ , x) , e₁) (η₀ x)
            same-point = ap (λ q → u (γ₀ , x) , q) (Δ-set _ _ e₁ (uo (γ₀ , x)))

          same : (@♭ h h′ : S₀ → D) (@♭ H : (a : F γ₀) → h (η₀ a) ≡ h′ (η₀ a))
               → pre (lift h) ≡ pre (lift h′)
          same h h′ H = ap (λ k → over-map (λ x → p (u x) , k x) (λ x → refl ∙ uo x))
            (fe (λ x → fe (λ e →
              at-γ₀ h h′ H (fst x) (sym (uo x) ∙ e) (snd x) e)))

          boxed : (@♭ h h′ : S₀ → D) (@♭ H : (a : F γ₀) → h (η₀ a) ≡ h′ (η₀ a))
                → box (lift h) ≡ box (lift h′)
          boxed h h′ H = sym (retraction U (box (lift h)))
            ∙ ap (inverse U) (box-crisp-path (same h h′ H))
            ∙ retraction U (box (lift h′))

        unique₀ : (@♭ h h′ : S₀ → D) (@♭ H : (a : F γ₀) → h (η₀ a) ≡ h′ (η₀ a))
                → (z : S₀) → h z ≡ h′ z
        unique₀ h h′ H (t , e₀) =
          ap (λ (w : ♭ (MapOver p (fst {B = D̂})))
                → snd (function (counit w) t) (triangle (counit w) t ∙ e₀))
             (boxed h h′ H)

  -- 4–5.
  module WithDecisions (@♭ δ : Decision Γ) (@♭ δ′ : Decision Γ′) where

    module OK = OverBase Γ-set closed-Γ closed-total K δ
    module OK′ = OverBase Γ′-set closed-Γ′ closed-total′ K′ δ′

    module AtCrisp (@♭ γ′ : Γ′) where

      fib′-discrete : Discrete (Output.family K′ γ′)
      fib′-discrete = FiberDiscrete.discrete dΓ′ (Output.total-discrete K′)
        (Output.projection K′) γ′

      fib-discrete : Discrete (Output.family K (g γ′))
      fib-discrete = FiberDiscrete.discrete dΓ (Output.total-discrete K)
        (Output.projection K) (g γ′)

      module Inv = OK.Fib.Target (g γ′) (Output.family K′ γ′)
        (Output.family-set K′ γ′) fib′-discrete (OK′.family-closed γ′)
      module Ret = OK′.Fib.Target γ′ (Output.family K′ γ′)
        (Output.family-set K′ γ′) fib′-discrete (OK′.family-closed γ′)
      module Sec = OK.Fib.Target (g γ′) (Output.family K (g γ′))
        (Output.family-set K (g γ′)) fib-discrete (OK.family-closed (g γ′))

      inv : Output.family K (g γ′) → Output.family K′ γ′
      inv = Inv.rec₀ (Output.family-unit K′ γ′)

      ret : (z : Output.family K′ γ′) → inv (C.comparison γ′ z) ≡ z
      ret = Ret.unique₀ (λ z → inv (C.comparison γ′ z)) (λ z → z)
        (λ a → ap inv (C.comparison-on-unit γ′ a)
               ∙ Inv.rec₀-η (Output.family-unit K′ γ′) a)

      sec : (y : Output.family K (g γ′)) → C.comparison γ′ (inv y) ≡ y
      sec = Sec.unique₀ (λ y → C.comparison γ′ (inv y)) (λ y → y)
        (λ a → ap (C.comparison γ′) (Inv.rec₀-η (Output.family-unit K′ γ′) a)
               ∙ C.comparison-on-unit γ′ a)

      equivalence : IsEquiv (C.comparison γ′)
      equivalence = set-equiv (Output.family-set K (g γ′)) inv sec ret

    fibres : C.ComparisonIsEquivalence
    fibres = discrete-ind dΓ′ (λ γ′ → IsEquiv (C.comparison γ′))
      (λ γ′ → AtCrisp.equivalence γ′)

  statement-B : Statement-B
  statement-B δ δ′ = WithDecisions.fibres δ δ′
