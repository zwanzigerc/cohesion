{-# OPTIONS --cohesion --without-K --flat-split #-}

-- From a relative shape of a family A over a discrete base, a relative shape
-- of the family of SET TRUNCATIONS b ↦ τ₀ (A b), ON THE SAME CARRIER:
--
--   truncate-payload : (@♭ K : RelativeShapeOver B dB A)
--                    → RelativeShapeOver B dB (λ b → τ₀ (A b))
--   unit-β : family-unit (truncate-payload K) b ∣ a ∣₀ ≡ family-unit K b a
--
-- Claude (Fable), 14 November 2026; fable-impl-22. A client of the
-- set-truncation interface of OrdinaryTruncation, included because
-- HANDOFF-37 asks that this call be kept possible, and at root's word of
-- 14 November. The construction is SHAPE0-TRUNCATE-EXISTING-PAYLOAD-01,
-- sections 1 to 3 (root; reviewed in FABLE-SET-PROOF-ASSESSMENT-01,
-- section 3). Its section 4, the transfer of the comparison, is NOT here:
-- it belongs to the proof plan.
--
-- Nothing is postulated and nothing is declared: no new shape, no new
-- relative payload. The total, its discreteness, the projection and the
-- sethood of its fibres are the fields of K, unchanged. The unit is the
-- old unit extended along ∣_∣₀ in each fibre, by the recursor of τ₀ into
-- the set Fiber p b. The universal field is proved from the old one.
--
-- WHAT IS USED OF THE TRUNCATION: the carrier, the unit, the NON-DEPENDENT
-- recursor into sets of the same level, its pointwise unit law and
-- pointwise uniqueness. Not the sethood of the carrier, no dependent
-- elimination, nothing at another level. FURTHER HYPOTHESIS: function
-- extensionality at the level ℓ (ShapeChoice.FunExtAt, the hypothesis of
-- the choice lemmas). The structure τ and fe are CRISP, because the
-- restriction, its inverse and their laws are used under box; their
-- operations act on ordinary points and maps.
--
-- THE PROOF OF THE UNIVERSAL FIELD. For a crisp test map q : D → B with set
-- fibres, write pre and pre₀ for precomposition with the old and the new
-- unit, as maps of MapOver records.
--   (1) restrict, evaluation of both fields at (b , ∣ a ∣₀), is an
--       equivalence MapOver fst₀ q → MapOver fst q: a MapOver record out of
--       a total space is a family (b : B) → F b → Fiber q b, with both round
--       trips by conversion, and on families restrict is fibrewise
--       precomposition with ∣_∣₀.
--   (2) restrict (pre₀ n) ≡ pre n, from the unit law in the fibres.
--   (3) flat-map restrict is an equivalence, flat-map pre is one by the
--       universal field of K, and (2) holds under box. Two out of three.
-- An identification of two MapOver records is obtained from a pointwise
-- identification of the families by one ap and two uses of fe; there is no
-- path algebra on triangles.
--
-- K NEED NOT BE MATCHED. Output.Total and Output.projection compute on the
-- constructor only, so a result defined by matching K would have its total
-- and projection stuck at a variable K, and unit-β could not even be
-- stated (the compiler refused that first version: the two sides lay in
-- different types). truncate-payload K is therefore built from the Output
-- projections of K: it IS a constructor form for every K, its total and
-- projection reduce to those of K by conversion (same-total, same-projection
-- are refl), and unit-β is a path in the fibre of the old projection. A
-- client that holds its payloads as variables can use the lemmas as they
-- stand. (This replaces remark 3 (a) of FABLE-SET-PROOF-ASSESSMENT-01.)
module TruncatedPayload where

open import Foundations
open import NativeSharp using (box-crisp-path)
open import Adjointify using (quasi-inverse)
open import RelativeSliceShape
open import ShapeChoice using (FunExtAt)
open import OrdinaryTruncation

module Truncate {@♭ ℓ : Level} (@♭ τ : SetTruncation ℓ) (@♭ fe : FunExtAt ℓ)
  {@♭ B : Set ℓ} {@♭ dB : Discrete B} {@♭ A : B → Set ℓ} where

  open SetTruncation τ

  A₀ : B → Set ℓ
  A₀ b = τ₀ (A b)

  ----------------------------------------------------------------------
  -- 1. Maps over B out of a total space, as families of maps into the
  --    fibres. Both round trips hold by conversion (eta for the record,
  --    for Σ and for functions).

  module Over (@♭ D : Set ℓ) (@♭ q : D → B) (@♭ qf : SetFibers q) where

    Family : (B → Set ℓ) → Set ℓ
    Family F = (b : B) → F b → Fiber q b

    curry : {F : B → Set ℓ} → MapOver (fst {B = F}) q → Family F
    curry M b a = function M (b , a) , triangle M (b , a)

    uncurry : {F : B → Set ℓ} → Family F → MapOver (fst {B = F}) q
    uncurry g = over-map (λ x → fst (g (fst x) (snd x)))
                         (λ x → snd (g (fst x) (snd x)))

    -- Evaluation of both fields at (b , ∣ a ∣₀). No right-unit path.
    restrict : MapOver (fst {B = A₀}) q → MapOver (fst {B = A}) q
    restrict M = over-map (λ x → function M (fst x , ∣ snd x ∣₀))
                          (λ x → triangle M (fst x , ∣ snd x ∣₀))

    extend : MapOver (fst {B = A}) q → MapOver (fst {B = A₀}) q
    extend N = uncurry (λ b → τ₀-rec (qf b) (curry N b))

    restrict-extend : (N : MapOver (fst {B = A}) q)
                    → restrict (extend N) ≡ N
    restrict-extend N = ap (uncurry {F = A})
      (fe (λ b → fe (λ a → τ₀-rec-unit (qf b) (curry N b) a)))

    extend-restrict : (M : MapOver (fst {B = A₀}) q)
                    → extend (restrict M) ≡ M
    extend-restrict M = ap (uncurry {F = A₀})
      (fe (λ b → fe (λ z →
        τ₀-unique (qf b)
          (τ₀-rec (qf b) (curry (restrict M) b)) (curry M b)
          (τ₀-rec-unit (qf b) (curry (restrict M) b)) z)))

    restrict♭ : ♭ (MapOver (fst {B = A₀}) q) → ♭ (MapOver (fst {B = A}) q)
    restrict♭ = flat-map restrict

    private
      restrict♭-extend : (y : ♭ (MapOver (fst {B = A}) q))
                       → restrict♭ (flat-map extend y) ≡ y
      restrict♭-extend (box N) = box-crisp-path (restrict-extend N)

      extend-restrict♭ : (x : ♭ (MapOver (fst {B = A₀}) q))
                       → flat-map extend (restrict♭ x) ≡ x
      extend-restrict♭ (box M) = box-crisp-path (extend-restrict M)

    restrict♭-equiv : IsEquiv restrict♭
    restrict♭-equiv =
      quasi-inverse (flat-map extend) restrict♭-extend extend-restrict♭

    restrict♭-injective : {u v : ♭ (MapOver (fst {B = A₀}) q)}
                        → restrict♭ u ≡ restrict♭ v → u ≡ v
    restrict♭-injective {u} {v} e =
      sym (retraction restrict♭-equiv u)
      ∙ ap (inverse restrict♭-equiv) e
      ∙ retraction restrict♭-equiv v

  ----------------------------------------------------------------------
  -- 2. The construction on the seven components of a payload.

  module OnComponents (@♭ S : Set ℓ) (@♭ dS : Discrete S)
    (@♭ p : S → B) (@♭ pf : SetFibers p)
    (@♭ η : Σ B A → S) (@♭ η-over : UnitOver B A S p η)
    (@♭ universal : SliceUniversal B A S p η η-over) where

    unit-fibre : (b : B) → A b → Fiber p b
    unit-fibre b a = η (b , a) , η-over (b , a)

    -- The old unit, extended along ∣_∣₀ in the fibre over b.
    ν : (b : B) → A₀ b → Fiber p b
    ν b = τ₀-rec (pf b) (unit-fibre b)

    ν-unit : (b : B) (a : A b) → ν b ∣ a ∣₀ ≡ unit-fibre b a
    ν-unit b = τ₀-rec-unit (pf b) (unit-fibre b)

    η₀ : Σ B A₀ → S
    η₀ x = fst (ν (fst x) (snd x))

    η₀-over : UnitOver B A₀ S p η₀
    η₀-over x = snd (ν (fst x) (snd x))

    module Test (@♭ D : Set ℓ) (@♭ dD : Discrete D)
      (@♭ q : D → B) (@♭ qf : SetFibers q) where

      open Over D q qf

      pre : MapOver p q → MapOver (fst {B = A}) q
      pre = precomposeOver B A S p η η-over D q

      pre₀ : MapOver p q → MapOver (fst {B = A₀}) q
      pre₀ = precomposeOver B A₀ S p η₀ η₀-over D q

      private
        push : MapOver p q → {b : B} → Fiber p b → Fiber q b
        push n w = function n (fst w) , (triangle n (fst w) ∙ snd w)

      -- The two precompositions agree after restriction (ordinary n).
      square : (n : MapOver p q) → restrict (pre₀ n) ≡ pre n
      square n = ap (uncurry {F = A})
        (fe (λ b → fe (λ a → ap (push n) (ν-unit b a))))

      private
        square♭ : (x : ♭ (MapOver p q))
                → restrict♭ (flat-map pre₀ x) ≡ flat-map pre x
        square♭ (box n) = box-crisp-path (square n)

        old : IsEquiv (flat-map pre)
        old = universal D dD q qf

        back : ♭ (MapOver (fst {B = A₀}) q) → ♭ (MapOver p q)
        back y = inverse old (restrict♭ y)

        back-pre₀ : (x : ♭ (MapOver p q)) → back (flat-map pre₀ x) ≡ x
        back-pre₀ x = ap (inverse old) (square♭ x) ∙ retraction old x

        pre₀-back : (y : ♭ (MapOver (fst {B = A₀}) q))
                  → flat-map pre₀ (back y) ≡ y
        pre₀-back y = restrict♭-injective
          (square♭ (back y) ∙ section old (restrict♭ y))

      universal₀ : IsEquiv (flat-map pre₀)
      universal₀ = quasi-inverse back pre₀-back back-pre₀

    truncated : RelativeShapeOver B dB A₀
    truncated = shape-over S dS p pf η₀ η₀-over
      (λ D dD q qf → Test.universal₀ D dD q qf)

  ----------------------------------------------------------------------
  -- 3. On a payload, through its Output projections.

  module OnPayload (@♭ K : RelativeShapeOver B dB A) =
    OnComponents (Output.Total K) (Output.total-discrete K)
      (Output.projection K) (Output.family-set K)
      (Output.unit K) (Output.unit-over K) (Output.universal K)

  truncate-payload : (@♭ K : RelativeShapeOver B dB A)
                   → RelativeShapeOver B dB A₀
  truncate-payload K = OnPayload.truncated K

  -- The carrier and the projection are the old ones, by conversion.
  same-total : (@♭ K : RelativeShapeOver B dB A)
             → Output.Total (truncate-payload K) ≡ Output.Total K
  same-total K = refl

  same-projection : (@♭ K : RelativeShapeOver B dB A) (x : Output.Total K)
                  → Output.projection (truncate-payload K) x
                    ≡ Output.projection K x
  same-projection K x = refl

  -- The new unit at a truncation unit is the old unit, as a point of the
  -- fibre of the projection: both components, the triangle included.
  unit-β : (@♭ K : RelativeShapeOver B dB A) (b : B) (a : A b)
         → Output.family-unit (truncate-payload K) b ∣ a ∣₀
           ≡ Output.family-unit K b a
  unit-β K = OnPayload.ν-unit K

  -- On total spaces: the new unit after (b , a) ↦ (b , ∣ a ∣₀) is the old
  -- unit. (What carries a Nullstellensatz of the old payload to the new.)
  unit-on-total : (@♭ K : RelativeShapeOver B dB A) (x : Σ B A)
                → Output.unit (truncate-payload K) (fst x , ∣ snd x ∣₀)
                  ≡ Output.unit K x
  unit-on-total K x = ap fst (unit-β K (fst x) (snd x))
