{-# OPTIONS --cohesion --without-K --flat-split #-}

-- THE STAGED SET-SOURCE CLIENT, APPLICATION: from the theorem of the
-- kernel at the declared closed data to the canonical comparison of the
-- dependent Bool/Code diagram AT AN OPEN CRISP POINT.
-- Claude (Fable), 14 November 2026; fable-impl-23
-- (FABLE-PLAN-SET-SOURCE-01, sections 11.1, 11.2 and 11.3 b;
-- SET-MAIN-FIXED-DATA-AND-STAGING-01, last section).
--
-- NOTHING IS DECLARED HERE, and no hypothesis is discharged. This module
-- is the composition, checked natively:
--
--   KernelTheorem            the type Statement-M of the kernel at the 21
--                            declared choices and 5 certificates of stages
--                            1 to 5. A CLOSED type. Its proof is Opus's;
--                            here it is an argument.
--   Under Z                  the type of proofs of Z from the eleven
--                            ordinary hypotheses at those data
--   whole                    KernelTheorem → Under (the comparison
--                            of the ORIGINAL payloads MB, MC of the whole
--                            diagram is an equivalence, in total form)
--                            (fibrewise, the accepted transfer of Opus,
--                            FromFibres.total)
--   At.local                 for crisp b : Bool and v : Code b, with NO
--                            point chosen: the canonical comparison of the
--                            two contextual captures of the diagram at
--                            (b , v) is an equivalence on every fibre
--                            (KernelFrom MB MC, from-kernel)
--   At.unit-law              its law on units, with no hypothesis
--
-- The eleven hypotheses are about the closed data only. Nothing of them,
-- of the kernel or of the 21 choices is transported to the point.
--
-- What this module does NOT say: that KernelTheorem is inhabited; that
-- the hypotheses hold in any model; anything about a diagram other than
-- this one.
module SetSourceApplication where

open import Foundations
open import Agda.Builtin.Bool using (Bool)
open import RelativeSliceShape
open import GlobalPrecohesion
  using (ʃ-discrete; PreservesProduct; Nullstellensatz; EpiC; MonoC)
open import DependentContextFixtures using (Code)
open import DependentDiagramFixtures using (BaseC; Fam; baseMap)
open import DiagramBundle using (module AssembleCaptured)
open import StagedDiagramClient using (module Local)
open import SetSourceStage5 public
import SetSourceKernelStatements as Statements

------------------------------------------------------------------------
-- 1. The statement of the kernel at the declared data. Closed.

KernelTheorem : Set₃
KernelTheorem = K5.Statement-M

-- The eleven ordinary hypotheses, spelled at the declared data, in the
-- order of the kernel: one MonoC; a product law and a Nullstellensatz for
-- each of X and Y; the product law and the Nullstellensatz of the closed
-- classifier; an EpiC and a Nullstellensatz for each attachment.
-- `Under Z` is the type of proofs of Z from them.
--
-- A function type, NOT a record: a record or data declaration with a
-- field whose type mentions the attachment (Nullstellensatz sPow, for
-- one) exhausts a 3 GB heap in this client, while the same types in a
-- function type are accepted at once. See the report of the increment.
Under : ∀ {a} → Set a → Set (lsuc ℓ₂ ⊔ a)
Under Z =
    MonoC K1.Pr.F-discrete sO sE
  → PreservesProduct saX saX saaX → Nullstellensatz K1.sX
  → PreservesProduct saY saY saaY → Nullstellensatz K1.sY
  → PreservesProduct sOj sOj sOO → Nullstellensatz sC
  → EpiC (ʃ-discrete sU) sU sPow → Nullstellensatz sPow
  → EpiC (ʃ-discrete sU′) sU′ sPow′ → Nullstellensatz sPow′
  → Z

-- The statement of the kernel is exactly this, by conversion.
kernel-is : KernelTheorem ≡ Under (IsEquiv K1.D.comparison-total)
kernel-is = refl

------------------------------------------------------------------------
-- 2. The whole diagram: from the truncated payloads to the original ones.

module AF = Statements.ArbitraryFibres τ fe₀₀ WB WC dWB dWC WA wf MB MC

-- The conclusion of the kernel is about the truncated payloads K₀, K₀′.
truncated : KernelTheorem → Under K1.D.ComparisonIsEquivalence
truncated theorem mc ppX nsX ppY nsY ppO nsC ec ns ec′ ns′ =
  K5.fibrewise (theorem mc ppX nsX ppY nsY ppO nsC ec ns ec′ ns′)

-- The comparison of the ORIGINAL payloads, in total form.
whole : KernelTheorem → Under AF.D.TotalComparisonIsEquivalence
whole theorem mc ppX nsX ppY nsY ppO nsC ec ns ec′ ns′ = AF.to-total
  (truncated theorem mc ppX nsX ppY nsY ppO nsC ec ns ec′ ns′)

------------------------------------------------------------------------
-- 3. At an open crisp point of the context. No point is chosen.

module At (@♭ b : Bool) (@♭ v : Code b) where

  open Local b v using (cells)

  module D = AssembleCaptured fe₀₀ cells

  -- The declared payloads are payloads of the whole diagram of THIS
  -- bundle: the module application is the check.
  module KF = D.KernelFrom MB MC

  -- The canonical comparison of the two contextual captures at (b , v).
  comparison : (k : BaseC b v)
             → Output.family D.reflC k
             → Output.family D.reflB (baseMap b v k)
  comparison = D.Diagram.comparison

  unit-law : (k : BaseC b v) (a : Fam b v (baseMap b v k))
           → comparison k (Output.family-unit D.reflC k a)
             ≡ Output.family-unit D.reflB (baseMap b v k) a
  unit-law = D.Diagram.comparison-on-unit

  -- THE APPLICATION.
  local : KernelTheorem → Under ((k : BaseC b v) → IsEquiv (comparison k))
  local theorem mc ppX nsX ppY nsY ppO nsC ec ns ec′ ns′ = D.from-kernel
    (KF.kernel (whole theorem mc ppX nsX ppY nsY ppO nsC ec ns ec′ ns′))
