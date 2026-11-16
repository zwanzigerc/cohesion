{-# OPTIONS --cohesion --without-K --flat-split #-}

-- SIGNATURE PROBE for FABLE-PLAN-SET-SOURCE-01.txt: the telescope of the
-- proof kernel of the set-source theorem, and the statements of its
-- stages as types. Claude (Fable), 14 November 2026.
-- Checked against the frozen fable-impl-22 with the two accepted modules
-- of Opus (PointsPieces, ComparisonTransfer) on the include path. NOT
-- part of any tree.
--
-- It contains
--   * the fixed data of SET-MAIN-FIXED-DATA-AND-STAGING-01 as ONE nested
--     telescope of crisp parameters: the ordinary structure, the diagram,
--     21 terminal shape choices and 5 larger-target certificates;
--   * the definitions without which the telescope cannot be written: the
--     closed endpoint `bottom`, the attachment as a quotient (its carrier
--     and generators; no property of it), the action of the closed
--     reflection on a map of level i;
--   * the statements of the stages O, C, I, T and M as types, and the
--     statement of stage B for an arbitrary closed diagram;
--   * the variant of section 12.7 of the plan (the attachments over the
--     original bases), as a sibling of the default telescope;
--   * three one-line compositions of ACCEPTED lemmas at the instances in
--     which the plan uses them (mere-section, fibrewise, to-total).
-- It contains NO PROOF of a statement of the plan. Nothing is postulated
-- and nothing is declared. The eleven ordinary hypotheses occur only in
-- the types of statements, never as module parameters.
--
-- LEVELS. i crisp; j = lsuc i; k = lsuc j. No type above k is formed
-- except the types of shape data and of the bounded Merely over k.
module SetSourceKernelStatements where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Foundations
open import CaptureContext using (Raise; raise; lower)
open import NativeSharp using (♯; sharp-unit)
open import GlobalPrecohesion
  using (ShapeData; ʃ; ʃ-set; ʃ-discrete; η; Merely; points-to-pieces;
         Nullstellensatz; PreservesProduct; EpiC; MonoC)
open import GlobalPropositions using (FunExt₂)
open import SmallPropositions using (PropExt)
open import ShapeChoice using (FunExtAt)
open import LargeTarget using (LargeOn)
open import BaseClassifier using (O)
open import PrincipalFilter using (module Principal)
open import RelativeSliceShape
open import ReindexingAssembly using (module TotalForm)
open import TotalBridge using (module TotalData)
open import TruncationDiscrete using (_⊎_; inl; inr)
open import OrdinaryTruncation
open import OrdinaryTruncationCompat using (to-global)
open import SmallQuotient
open import QuotientTruncations using (module FromQuotients)
open import ClosedReflection using (Closed; module Reflection)
open import ClosedReflectionRaised using (module AtSupport)
open import PointsPieces using (PointsSection; merely-points-section)
import ComparisonTransfer

------------------------------------------------------------------------
-- 0. The attachment of stage I, as a quotient. DEFINITIONS ONLY: the
--    carrier, the generators and the attaching path. Its universal
--    property into sets, uniqueness and the cover by generators are
--    statements of the plan (I1) and are not here.
--
--    For a map m : Dm → Bt of level a and a type Tag of level t with two
--    points, it is the set pushout of
--        Bt × Bool  ←  Dm × Bool  →  Dm × Tag,
--        (m a , t)  ↤   (a , t)   ↦  (a , end t),
--    at the level a ⊔ t. The sum and the Σ-types are level-heterogeneous,
--    so no lift occurs. The kernel uses it at (a , t) = (j , k); the
--    variant of section 12.7 of the plan uses it at (i , k).

data Closure {ℓ : Level} {L : Set ℓ} (Edge : L → L → Set ℓ)
     : L → L → Set ℓ where
  edge  : {l n : L} → Edge l n → Closure Edge l n
  same  : {l : L} → Closure Edge l l
  back  : {l n : L} → Closure Edge l n → Closure Edge n l
  chain : {l n o : L} → Closure Edge l n → Closure Edge n o
        → Closure Edge l o

module Attachment {a t : Level}
  (Q : Quotients (a ⊔ t)) (T : PropTruncation (a ⊔ t))
  {Dm Bt : Set a} (m : Dm → Bt)
  {Tag : Set t} (e₀ e₁ : Tag) where

  open Quotients Q
  open PropTruncation T

  end : Bool → Tag
  end false = e₀
  end true = e₁

  Presentation : Set (a ⊔ t)
  Presentation = (Bt × Bool) ⊎ (Dm × Tag)

  Edge : Presentation → Presentation → Set (a ⊔ t)
  Edge l n = Σ (Dm × Bool) (λ e →
    (l ≡ inl (m (fst e) , snd e)) × (n ≡ inr (fst e , end (snd e))))

  relation : EquivRel Presentation
  relation = record
    { _≈_ = λ l n → ∥ Closure Edge l n ∥
    ; ≈-prop = λ l n → squash
    ; ≈-refl = λ l → ∣ same ∣
    ; ≈-sym = λ l n → ∥-map back
    ; ≈-trans = λ l n o r s →
        ∥-rec squash (λ a → ∥-rec squash (λ b → ∣ chain a b ∣) s) r
    }

  U : Set (a ⊔ t)
  U = Presentation / relation

  present : Presentation → U
  present = [_] {R = relation}

  vertex : Bool → Bt → U
  vertex t b = present (inl (b , t))

  middle : Dm → Tag → U
  middle a z = present (inr (a , z))

  attach : (a : Dm) (t : Bool) → vertex t (m a) ≡ middle a (end t)
  attach a t = sound {R = relation} (inl (m a , t)) (inr (a , end t))
    ∣ edge ((a , t) , refl , refl) ∣

------------------------------------------------------------------------
-- 1. Stage B, for an arbitrary closed diagram of one level: the canonical
--    comparison of a closed diagram with decidable-up-to-P equality on its
--    two bases is an equivalence on every fibre. The two decisions are
--    crisp WHOLE functions; no continuity, product or Nullstellensatz
--    hypothesis occurs.

module ClosedComparison {@♭ ℓ : Level}
  (@♭ fe : FunExt₂ ℓ ℓ) (@♭ T : PropTruncation ℓ)
  (@♭ P : Set ℓ) (@♭ P-prop : IsProp P) (@♭ dP : Discrete P)
  (@♭ Γ Γ′ : Set ℓ) (@♭ dΓ : Discrete Γ) (@♭ dΓ′ : Discrete Γ′)
  (@♭ Γ-set : IsSet Γ) (@♭ Γ′-set : IsSet Γ′)
  (@♭ closed-Γ : Closed P Γ) (@♭ closed-Γ′ : Closed P Γ′)
  (@♭ A : Γ → Set ℓ) (@♭ closed-total : Closed P (Σ Γ A))
  (@♭ g : Γ′ → Γ)
  (@♭ K : RelativeShapeOver Γ dΓ A)
  (@♭ K′ : RelativeShapeOver Γ′ dΓ′ (A ∘ g)) where

  open PropTruncation T

  Decision : Set ℓ → Set ℓ
  Decision V = (x y : V) → ∥ (x ≡ y) ⊎ ((x ≡ y) → P) ∥

  module C = TotalForm Γ Γ′ dΓ dΓ′ A g K K′

  Statement-B : Set ℓ
  Statement-B = (@♭ δ : Decision Γ) (@♭ δ′ : Decision Γ′)
              → C.ComparisonIsEquivalence

------------------------------------------------------------------------
-- 2. The kernel. Each module adds crisp parameters to those above it,
--    and no module has an ordinary parameter.

module Kernel {@♭ i : Level}
  -- extensionality at the five pairs of levels of the proof
  (@♭ fe-i : FunExt₂ i i) (@♭ fe-j : FunExt₂ (lsuc i) (lsuc i))
  (@♭ fe-k : FunExt₂ (lsuc (lsuc i)) (lsuc (lsuc i)))
  (@♭ fe-ij : FunExt₂ i (lsuc i))
  (@♭ fe-jk : FunExt₂ (lsuc i) (lsuc (lsuc i)))
  (@♭ pe-i : PropExt i) (@♭ pe-j : PropExt (lsuc i))
  -- ordinary small quotients at j, with effectivity, and at k
  (@♭ Qj : Quotients (lsuc i)) (@♭ Ej : Eliminates Qj (lsuc i))
  (@♭ effective-j : Effective Qj)
  (@♭ Qk : Quotients (lsuc (lsuc i)))
  (@♭ Ek : Eliminates Qk (lsuc (lsuc i)))
  -- the diagram: discrete set bases, set fibres, the two payloads
  (@♭ B B′ : Set i) (@♭ dB : Discrete B) (@♭ dB′ : Discrete B′)
  (@♭ B-set : IsSet B) (@♭ B′-set : IsSet B′)
  (@♭ A : B → Set i) (@♭ A-set : (b : B) → IsSet (A b))
  (@♭ f : B′ → B)
  (@♭ K : RelativeShapeOver B dB A)
  (@♭ K′ : RelativeShapeOver B′ dB′ (A ∘ f))
  -- choice 1 of 21: the shape of the sharp of the classifier at i
  (@♭ sO : ShapeData (♯ (O i)))
  where

  -- Both truncations are made from the quotients.
  Tj : PropTruncation (lsuc i)
  Tj = FromQuotients.prop-truncation Qj Ej

  Tk : PropTruncation (lsuc (lsuc i))
  Tk = FromQuotients.prop-truncation Qk Ek

  -- The canonical comparison of the diagram.
  module D = TotalForm B B′ dB dB′ A f K K′

  X : Set i
  X = Σ B A

  Y : Set i
  Y = Σ B′ (A ∘ f)

  -- The terminal data of the two totals: carrier and unit those of the
  -- payloads. Derived; not choices.
  sX : ShapeData X
  sX = TotalData.total-data fe-i B-set K

  sY : ShapeData Y
  sY = TotalData.total-data fe-i B′-set K′

  -- F, Q, P, R, C of fable-impl-20, formed from sO alone.
  module Pr = Principal sO

  module Support
    -- choices 2 to 6, and certificate 1 of 5
    (@♭ sQ : ShapeData Pr.Q) (@♭ sR : ShapeData Pr.R)
    (@♭ sE : ShapeData (Pr.F → ♯ (O i)))
    (@♭ sYQ : ShapeData (♯ Pr.Q))
    (@♭ cQ : LargeOn (lsuc (lsuc i)) sYQ)
    (@♭ sOj : ShapeData (♯ (O (lsuc i))))
    where

    module Qd = Pr.Quantified sQ fe-i pe-i fe-j
    module Cl = Qd.Closed sR pe-j fe-jk
    module Sp = Cl.Split (to-global Tj)
    module Cm = Qd.Compared sE sYQ cQ sOj pe-j

    P : Set (lsuc i)
    P = Pr.P

    C : Set (lsuc (lsuc i))
    C = Pr.C

    -- The false endpoint of the closed classifier: the code of P.
    bottom : C
    bottom = Qd.p , Cl.path-from Qd.p Qd.P-to-p

    -- The closed reflection at the support, for sets of level i. The
    -- level of Rf is WRITTEN i ⊔ lsuc i, as AtSupport writes it: with
    -- lsuc i the conversion of Rf.c with CP.cP at this support does not
    -- finish in ten minutes (the two copies are then compared
    -- structurally, through the proof that P is a proposition).
    module Rf = Reflection {i ⊔ lsuc i} Qj Ej Tj P Qd.P-is-prop
    module CP = AtSupport {i} {lsuc i} Qj Ej Tj P Qd.P-is-prop Qd.P-discrete

    cP-map : {V W : Set i} → (V → W) → CP.cP V → CP.cP W
    cP-map g = Rf.c-map (λ r → raise (g (lower r)))

    Decision : Set (lsuc i) → Set (lsuc i)
    Decision V =
      (x y : V) → PropTruncation.∥_∥ Tj ((x ≡ y) ⊎ ((x ≡ y) → P))

    -- The attachment for the diagonal of the closed reflection of V.
    module Att (@♭ V : Set i) where

      G : Set (lsuc i)
      G = CP.cP V

      module At = Attachment {lsuc i} {lsuc (lsuc i)} Qk Tk
        {Dm = G} {Bt = G × G} (λ x → x , x)
        (sharp-unit bottom) (sharp-unit Pr.truth-point)

      U : Set (lsuc (lsuc i))
      U = At.U

    -- THE VARIANT of section 12.7 of the plan: the attachment for the
    -- diagonal of the ORIGINAL base V, with no closed reflection in it.
    module AttI (@♭ V : Set i) where

      module At = Attachment {i} {lsuc (lsuc i)} Qk Tk
        {Dm = V} {Bt = V × V} (λ x → x , x)
        (sharp-unit bottom) (sharp-unit Pr.truth-point)

      U : Set (lsuc (lsuc i))
      U = At.U

    DecisionI : Set i → Set (lsuc i)
    DecisionI V =
      (x y : V) → PropTruncation.∥_∥ Tj ((x ≡ y) ⊎ ((x ≡ y) → P))

    -- I5 (variant). A decision on V descends to its closed reflection.
    Statement-I5 : Set (lsuc i)
    Statement-I5 = {V : Set i} → DecisionI V → Decision (CP.cP V)

    module Open
      -- choices 7 to 10, and certificates 2 to 5
      (@♭ saX : ShapeData (♯ (♭ X)))
      (@♭ saaX : ShapeData (♯ (♭ X) × ♯ (♭ X)))
      (@♭ caaX : LargeOn (lsuc i) saaX) (@♭ cX : LargeOn (lsuc i) sX)
      (@♭ saY : ShapeData (♯ (♭ Y)))
      (@♭ saaY : ShapeData (♯ (♭ Y) × ♯ (♭ Y)))
      (@♭ caaY : LargeOn (lsuc i) saaY) (@♭ cY : LargeOn (lsuc i) sY)
      where

      -- O1. Under the support, points-to-pieces of a total is an
      --     equivalence.
      Statement-O1-X : Set (lsuc i)
      Statement-O1-X = PreservesProduct saX saX saaX → Nullstellensatz sX
                     → P → IsEquiv (points-to-pieces sX)

      Statement-O1-Y : Set (lsuc i)
      Statement-O1-Y = PreservesProduct saY saY saaY → Nullstellensatz sY
                     → P → IsEquiv (points-to-pieces sY)

      -- O2. Hence, under the support, so is the canonical comparison.
      Statement-O2 : Set (lsuc i)
      Statement-O2 = (P → IsEquiv (points-to-pieces sX))
                   → (P → IsEquiv (points-to-pieces sY))
                   → P → IsEquiv D.comparison-total

      -- R3 at the comparison: joint detection for a map of level i.
      Statement-detect : Set (lsuc i)
      Statement-detect = (P → IsEquiv D.comparison-total)
                       → IsEquiv (cP-map D.comparison-total)
                       → IsEquiv D.comparison-total

      module Classifier
        -- choices 11 to 13
        (@♭ sOO : ShapeData (♯ (O (lsuc i)) × ♯ (O (lsuc i))))
        (@♭ sC : ShapeData (♯ C))
        (@♭ sLL : ShapeData (ʃ sC → ʃ sC))
        where

        L : Set (lsuc (lsuc i))
        L = ʃ sC

        -- C5. The shape of the sharp of the closed classifier is
        --     contractible.
        Statement-C5 : Set (lsuc (lsuc (lsuc i)))
        Statement-C5 = MonoC Pr.F-discrete sO sE
                     → PreservesProduct sOj sOj sOO → Nullstellensatz sC
                     → IsContr L

        -- M2. An ordinary contraction gives a crisp one.
        Statement-M2 : Set (lsuc (lsuc (lsuc i)))
        Statement-M2 = IsContr L → {Z : Set (lsuc (lsuc i))}
                     → ((@♭ ct : IsContr L) → Z) → Z

        module Attachments
          -- choices 14 to 21: four for each of the two closed bases
          (@♭ sU : ShapeData (Att.U B))
          (@♭ sPow : ShapeData (ʃ sU → Att.U B))
          (@♭ sSecH : ShapeData (ʃ sU → ♭ (Att.U B)))
          (@♭ sSecS : ShapeData (ʃ sU → ʃ sU))
          (@♭ sU′ : ShapeData (Att.U B′))
          (@♭ sPow′ : ShapeData (ʃ sU′ → Att.U B′))
          (@♭ sSecH′ : ShapeData (ʃ sU′ → ♭ (Att.U B′)))
          (@♭ sSecS′ : ShapeData (ʃ sU′ → ʃ sU′))
          where

          -- An accepted lemma at the instance used: the mere section.
          mere-section : EpiC (ʃ-discrete sU) sU sPow → Nullstellensatz sPow
                       → Merely (PointsSection sU)
          mere-section = merely-points-section sU sPow

          -- M1. A mere section gives, for a proposition of level k, a
          --     crisp section.
          Statement-M1 : Set (lsuc (lsuc (lsuc i)))
          Statement-M1 = Merely (PointsSection sU)
                       → (Z : Set (lsuc (lsuc i))) → IsProp Z
                       → ((@♭ σ : PointsSection sU) → Z) → Z

          Statement-M1′ : Set (lsuc (lsuc (lsuc i)))
          Statement-M1′ = Merely (PointsSection sU′)
                        → (Z : Set (lsuc (lsuc i))) → IsProp Z
                        → ((@♭ σ′ : PointsSection sU′) → Z) → Z

          -- I4. The decision of equality up to P on a closed base, as a
          --     function of a crisp section and a crisp contraction.
          Statement-I4 : Set (lsuc (lsuc i))
          Statement-I4 = (@♭ σ : PointsSection sU) (@♭ ct : IsContr L)
                       → Decision (Att.G B)

          Statement-I4′ : Set (lsuc (lsuc i))
          Statement-I4′ = (@♭ σ′ : PointsSection sU′) (@♭ ct : IsContr L)
                        → Decision (Att.G B′)

          -- T3. The closed core: from crisp witnesses alone, the closed
          --     reflection of the comparison is an equivalence. Stages I,
          --     B and T together; no ordinary hypothesis.
          Statement-T3 : Set (lsuc i)
          Statement-T3 = (@♭ δ : Decision (Att.G B))
                         (@♭ δ′ : Decision (Att.G B′))
                       → IsEquiv (cP-map D.comparison-total)

          -- M. The theorem of the kernel: three product laws, five
          --    Nullstellensatz instances, one MonoC, two EpiC.
          Statement-M : Set (lsuc (lsuc (lsuc i)))
          Statement-M =
              MonoC Pr.F-discrete sO sE
            → PreservesProduct saX saX saaX → Nullstellensatz sX
            → PreservesProduct saY saY saaY → Nullstellensatz sY
            → PreservesProduct sOj sOj sOO → Nullstellensatz sC
            → EpiC (ʃ-discrete sU) sU sPow → Nullstellensatz sPow
            → EpiC (ʃ-discrete sU′) sU′ sPow′ → Nullstellensatz sPow′
            → IsEquiv D.comparison-total

          -- An accepted lemma at the instance used: from the total
          -- comparison to the comparison on every fibre.
          fibrewise : IsEquiv D.comparison-total → D.ComparisonIsEquivalence
          fibrewise = D.FromTotal.fibres B′-set

        -- THE VARIANT of section 12.7: the eight attachment choices on
        -- the attachments of the ORIGINAL bases, and the decision for
        -- those bases. With I5 it replaces I4 and I4′; nothing else in
        -- the kernel changes. Not part of the default telescope.
        module AttachmentsOverBases
          (@♭ sU : ShapeData (AttI.U B))
          (@♭ sPow : ShapeData (ʃ sU → AttI.U B))
          (@♭ sSecH : ShapeData (ʃ sU → ♭ (AttI.U B)))
          (@♭ sSecS : ShapeData (ʃ sU → ʃ sU))
          (@♭ sU′ : ShapeData (AttI.U B′))
          (@♭ sPow′ : ShapeData (ʃ sU′ → AttI.U B′))
          (@♭ sSecH′ : ShapeData (ʃ sU′ → ♭ (AttI.U B′)))
          (@♭ sSecS′ : ShapeData (ʃ sU′ → ʃ sU′))
          where

          Statement-I4-base : Set (lsuc (lsuc i))
          Statement-I4-base = (@♭ σ : PointsSection sU) (@♭ ct : IsContr L)
                            → DecisionI B

          Statement-I4-base′ : Set (lsuc (lsuc i))
          Statement-I4-base′ =
            (@♭ σ′ : PointsSection sU′) (@♭ ct : IsContr L) → DecisionI B′

------------------------------------------------------------------------
-- 3. Stage Z, the generic part: arbitrary fibres. The accepted transfer
--    and the accepted passage from fibres to the total, composed in the
--    order of the staging document. A term, since both are accepted.

module ArbitraryFibres {@♭ ℓ : Level}
  (@♭ τ : SetTruncation ℓ) (@♭ fe : FunExtAt ℓ)
  (@♭ B B′ : Set ℓ) (@♭ dB : Discrete B) (@♭ dB′ : Discrete B′)
  (@♭ A : B → Set ℓ) (@♭ f : B′ → B)
  (@♭ K : RelativeShapeOver B dB A)
  (@♭ K′ : RelativeShapeOver B′ dB′ (A ∘ f)) where

  module CT = ComparisonTransfer.Proof τ fe B B′ dB dB′ A f K K′
  module D = TotalForm B B′ dB dB′ A f K K′

  -- The input is the conclusion of the kernel at the truncated payloads
  -- CT.K₀, CT.K′₀ (followed by `fibrewise`); the output is what
  -- DiagramAssembly.KernelFrom asks for.
  to-total : CT.C₀.ComparisonIsEquivalence → D.TotalComparisonIsEquivalence
  to-total e = D.FromFibres.total (CT.transfer e)
