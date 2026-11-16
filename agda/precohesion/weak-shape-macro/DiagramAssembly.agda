{-# OPTIONS --cohesion --without-K --flat-split #-}

-- The library core of automatic diagram assembly (step S1 of
-- AUTOMATIC-ASSEMBLY-PLAN-FABLE-01, with the interface refinements of
-- AUTOMATIC-ASSEMBLY-ROOT-DECISIONS-01 and
-- AUTOMATIC-ASSEMBLY-LIBRARY-PLAN-AUDIT-01). Claude (Fable), 13 November
-- 2026; fable-impl-11. Postulate-free; no reflection; no capture.
--
-- INPUT. A native diagram and the CLOSED payloads of its two whole total
-- sources. All data crisp, at one level ℓ.
--
--   Closed   f : C → B  a map of discrete SETS, A : B → Set ℓ arbitrary,
--            KB : Closed (Σ B A),  KC : Closed (Σ C (A ∘ f)).
--   Open     the same over a discrete type G with DECIDABLE equality (a
--            packed crisp context): B, C : G → Set ℓ families of discrete
--            sets, f : (g : G) → C g → B g, A : Σ G B → Set ℓ, and
--              KB : Closed (Σ (Σ G B) A)
--              KC : Closed (Σ (Σ G C) (A ∘ total-map)),
--            total-map (g , c) = (g , f g c).  Open.At g₀ is the diagram at
--            a crisp point g₀ of the context.
-- No decision procedure is asked of B, C, B g or C g. A carries no sethood
-- hypothesis. The module supplies no payload: both closed payloads are
-- arguments, so it is not a provider of shapes.
--
-- OPAQUE COPIES OF THE PAYLOADS. Each form first binds the two supplied
-- payloads, in an abstract block, to
--   payloadB, payloadC              which do not unfold outside the block
--   payloadB-path, payloadC-path    payloadB ≡ KB, payloadC ≡ KC
-- and derives EVERYTHING from the copies. Reason, an observation about
-- the tested cases and not a general criterion: when the library was
-- applied to the payload of a capture, to an alias of a payload or to a
-- bundle field, the tested statements about its raw outputs restated in a
-- client were not checked in ten minutes; with opaque copies the same
-- statements take seconds (diagnostics/payload-atoms; RESULTS-FABLE.txt,
-- section H). The mechanism is not established. The abstract blocks (one
-- in each form) introduce definitions, the copies and their paths, and no
-- axiom. The open form's block also binds the supplied decision procedure
-- of the context (`decision`): the derivation is generic in the decider,
-- and a client does not need it normalised at its points. The diagram
-- itself (bases, maps, family, discreteness, sethood) is NOT copied:
-- those are the client's native data and reduce as before.
--
-- (Wording of this paragraph and of the entry raw-reflB below corrected
-- after fable-impl-11, M11-DOCUMENTATION-CORRECTIONS-01 items 1, 2 and 8.
-- No definition of this module is changed.)
--
-- OUTPUT, the same names in both forms where they apply.
--
--   raw-reflB, raw-reflC   "raw" means: DERIVED FROM THE OPAQUE COPIES,
--                          WITHOUT THE FINAL SEAL (ClosedBridge,
--                          TotalConverse; in the open form restricted to
--                          the fibre of the context, DecidableRestriction).
--                          Closed form: their total carriers and units
--                          are those of the copies of the whole payloads.
--                          Open form, at g₀: their carriers and units are
--                          the fibre at g₀ of the reflections derived
--                          from the copies, and the unit of that fibre.
--                          In neither form is a definitional reduction to
--                          the carrier or unit of a SUPPLIED payload
--                          promised: the copies are the supplied payloads
--                          up to payloadB-path and payloadC-path only.
--   Kernel                 what a future theorem has to supply: the
--                          canonical comparison of the WHOLE closed diagram
--                          is an equivalence, in total form. An ORDINARY
--                          hypothesis wherever it occurs. It is the
--                          conclusion of that theorem for one diagram. It
--                          is not proved here, it is not an axiom, and it
--                          is not the list of that theorem's premises.
--                          In the open form it is GLOBAL: about the diagram
--                          Σ G C → Σ G B, never about a local one.
--   Whole                  the canonical comparison of the whole diagram
--                          (TotalForm), public under ONE spelling, with the
--                          whole data it is made of (closed form: totalB,
--                          totalC, raw-reflB, raw-reflC; open form: wholeB,
--                          wholeC, whole-reflB, whole-reflC and
--                          wholeB-discrete, wholeB-set, wholeC-discrete,
--                          wholeC-set). A proof of Kernel refers to these
--                          names and rebuilds nothing.
--   KernelFrom MB MC       Kernel from the same statement about ANY other
--                          reflections of the whole diagram: Supplied is
--                          their comparison, kernel the transfer
--                          (ReindexingChoice). This is the way in for a
--                          client that works with reflections derived from
--                          the ORIGINAL supplied payloads.
--   reflB, reflC           the DEFAULT outputs: the raw reflections SEALED
--                          (Sealed). A client may restate results about
--                          them in its own terms. Price: they are equal to
--                          the raw ones propositionally only (reflB-path,
--                          reflC-path).
--   Diagram                the canonical comparison of the diagram for the
--                          default outputs, in both forms, with its unit
--                          law Diagram.comparison-on-unit.
--   from-kernel, total-from-kernel
--                          Kernel gives the conclusion for Diagram.
--   raw-from-kernel        the same for the raw reflections: closed form
--                          Whole; open form Raw, the LOCAL diagram at g₀.
--   Sealing                ONE instance of ReindexingChoice.Independence
--                          for the pair (raw, default). Whole (closed) or
--                          Raw (open, local), Diagram, TotalBridgeC and
--                          BridgeB ARE its modules TK, TL, C′ and FC, under
--                          public names. Sealing.natural is the square
--                            Diagram.comparison-total (TotalBridgeC.forward z)
--                              ≡ Sealing.pull (Whole or Raw .comparison-total z)
--                          and Sealing.pull is BridgeB.forward in each
--                          fibre (pull-is).
--   natural                closed form only: that square with an explicit
--                          signature in the public names. At a point of the
--                          open form the same signature is not checked
--                          within the heap limit, here or in a client
--                          (diagnostics/open-naturality); there the square
--                          is Sealing.natural under its own type. It is in
--                          use all the same: from-kernel goes through
--                          Sealing.fibre-form and Transfer.total, whose
--                          proofs apply it.
--   BridgeB, BridgeC       the canonical comparisons between raw and
--                          default outputs, fibrewise, with their unit laws
--                          (ShapeChoice.FiberChoice). BridgeB is the FC of
--                          Sealing; BridgeC is an instance of its own.
--   TotalBridgeC           the canonical comparison raw → default on total
--                          spaces, C side (the C′ of Sealing).
--   decidable              the conclusion without Kernel when the two
--                          bases happen to have decidable equality
--                          (DecidableReindexing). Extra crisp arguments of
--                          this one export only.
--   ForPayloads MB MC      the same for any other reflections of the same
--                          diagram: Chosen (their comparison), FromRaw
--                          (the Independence instance against the raw
--                          outputs), from-kernel′, total-from-kernel′. MB
--                          and MC are RelativeShapeOver values. A fresh
--                          capture is not one; FromCapture turns a capture
--                          of a local total source into one, over a
--                          decidable context.
--   Open only              Specialised (ContextSpecialisation.Specialise for
--                          the copies) and, at a point, Point (its AtPoint),
--                          InclusionB, InclusionC (the comparisons along
--                          the inclusions of the fibres of the context),
--                          square (the whole/local square for ORDINARY
--                          points), raw-dataB, raw-dataC, whole-from-kernel.
--
-- POLICY ON SEALING (root decision Q4), the same in both forms: default
-- outputs sealed, raw outputs public under the names above, bridges
-- public. What is observed: natively restated results about the default
-- outputs are checked in seconds in every client of this tree; at a point
-- of the open form natively restated results about the raw outputs are
-- not checked within the limits. So state results about raw outputs in
-- the library's own terms (Whole.…, Raw.…). In the closed form the
-- restatements that the clients display did pass. None of this is a
-- bound for all uses.
--
-- LEVELS. G, the bases, the fibres of A, the total sources, all carriers
-- and all comparisons are at ℓ. Kernel and the comparison conclusions are
-- at ℓ. Closed X, ShapeData X, RelativeShapeOver, FunExtAt ℓ, and hence
-- the paths payloadB-path, reflB-path and their like, are at lsuc ℓ.
-- Nothing is resized.
module DiagramAssembly where

open import Foundations
open import RelativeSliceShape
import ShapeChoice
open ShapeChoice using (FunExtAt)
open import GlobalPrecohesion using (ShapeData; ʃ; η; Closed)
open import ClosedBridge using (closed-bridge)
import CapturedShape as C
open C using (CapturedShape)
open import DecidableBase using (DecEq; module CaptureFibre)
open import TotalConverse using (module Converse)
open import ReindexingAssembly using (module TotalForm)
open import ReindexingChoice using (module Independence)
open import DecidableReindexing using (module Stable)
open import ContextSpecialisation using (module Specialise)
open import Sealed using (sealed; sealed-path)

module _ {@♭ ℓ : Level} where

  ----------------------------------------------------------------------
  -- A closed diagram.

  module Closed
    (@♭ fe : FunExtAt ℓ)
    {@♭ B C : Set ℓ}
    (@♭ dB : Discrete B) (@♭ B-set : IsSet B)
    (@♭ dC : Discrete C) (@♭ C-set : IsSet C)
    (@♭ f : C → B) (@♭ A : B → Set ℓ)
    (@♭ KB : Closed (Σ B A)) (@♭ KC : Closed (Σ C (A ∘ f))) where

    -- The payloads as ATOMS. Everything below is derived from payloadB
    -- and payloadC, which do not unfold outside this block; the supplied
    -- KB and KC are used here and nowhere else.
    abstract
      payloadB : Closed (Σ B A)
      payloadB = KB

      payloadC : Closed (Σ C (A ∘ f))
      payloadC = KC

      payloadB-path : payloadB ≡ KB
      payloadB-path = refl

      payloadC-path : payloadC ≡ KC
      payloadC-path = refl

    -- Whole and raw data.
    totalB : ShapeData (Σ B A)
    totalB = closed-bridge fe (Σ B A) payloadB

    totalC : ShapeData (Σ C (A ∘ f))
    totalC = closed-bridge fe (Σ C (A ∘ f)) payloadC

    raw-reflB : RelativeShapeOver B dB A
    raw-reflB = Converse.relative fe {dΓ = dB} B-set totalB

    raw-reflC : RelativeShapeOver C dC (A ∘ f)
    raw-reflC = Converse.relative fe {dΓ = dC} C-set totalC

    -- Default outputs.
    reflB : RelativeShapeOver B dB A
    reflB = sealed raw-reflB

    reflC : RelativeShapeOver C dC (A ∘ f)
    reflC = sealed raw-reflC

    reflB-path : reflB ≡ raw-reflB
    reflB-path = sealed-path raw-reflB

    reflC-path : reflC ≡ raw-reflC
    reflC-path = sealed-path raw-reflC

    -- ONE instance of the comparison machinery for the pair (raw,
    -- default). Its four modules are exported under the public names, so
    -- that the type of Sealing.natural is literally
    --   Diagram.comparison-total (TotalBridgeC.forward z)
    --     ≡ Sealing.pull (Whole.comparison-total z).
    module Sealing = Independence fe B C dB dC A f raw-reflB reflB raw-reflC reflC
    open Sealing public using ()
      renaming (module TK to Whole; module TL to Diagram;
                module C′ to TotalBridgeC; module FC to BridgeB)

    -- The fibrewise bridge on the C side is an instance of its own.
    module BridgeC = ShapeChoice.FiberChoice fe raw-reflC reflC

    -- The square of the two comparisons with the bridges, in the public
    -- names. Sealing.pull is the B-side bridge in each fibre.
    natural : (z : Output.Total raw-reflC)
            → Diagram.comparison-total (TotalBridgeC.forward z)
              ≡ Sealing.pull (Whole.comparison-total z)
    natural = Sealing.natural

    pull-is : (w : Whole.PulledTotal)
            → Sealing.pull w ≡ (fst w , BridgeB.forward (f (fst w)) (snd w))
    pull-is w = refl

    Kernel : Set ℓ
    Kernel = Whole.TotalComparisonIsEquivalence

    raw-from-kernel : Kernel → Whole.ComparisonIsEquivalence
    raw-from-kernel = Whole.FromTotal.fibres C-set

    total-from-kernel : Kernel → Diagram.TotalComparisonIsEquivalence
    total-from-kernel = Sealing.Transfer.total

    from-kernel : Kernel → Diagram.ComparisonIsEquivalence
    from-kernel k = Diagram.FromTotal.fibres C-set (total-from-kernel k)

    decidable : (@♭ decB : DecEq B) (@♭ decC : DecEq C)
              → Diagram.ComparisonIsEquivalence
    decidable decB decC = Stable.fibres fe B C dB dC decB decC A f reflB reflC

    -- Kernel from the same statement about other reflections MB, MC of
    -- the diagram: Supplied is their comparison.
    module KernelFrom
      (@♭ MB : RelativeShapeOver B dB A)
      (@♭ MC : RelativeShapeOver C dC (A ∘ f)) where

      module ToWhole = Independence fe B C dB dC A f MB raw-reflB MC raw-reflC
      open ToWhole public using () renaming (module TK to Supplied)

      kernel : Supplied.TotalComparisonIsEquivalence → Kernel
      kernel = ToWhole.Transfer.total

    -- Any other reflections of the same diagram: Chosen is their
    -- comparison, FromRaw the naturality against the raw outputs.
    module ForPayloads
      (@♭ MB : RelativeShapeOver B dB A)
      (@♭ MC : RelativeShapeOver C dC (A ∘ f)) where

      module FromRaw = Independence fe B C dB dC A f raw-reflB MB raw-reflC MC
      open FromRaw public using () renaming (module TL to Chosen)

      total-from-kernel′ : Kernel → Chosen.TotalComparisonIsEquivalence
      total-from-kernel′ = FromRaw.Transfer.total

      from-kernel′ : Kernel → Chosen.ComparisonIsEquivalence
      from-kernel′ k = Chosen.FromTotal.fibres C-set (total-from-kernel′ k)

  ----------------------------------------------------------------------
  -- A diagram over a decidable context.

  module Open
    (@♭ fe : FunExtAt ℓ)
    {@♭ G : Set ℓ} {@♭ dG : Discrete G} (@♭ dec : DecEq G)
    {@♭ B C : G → Set ℓ}
    (@♭ dB : (@♭ g : G) → Discrete (B g)) (@♭ B-set : (g : G) → IsSet (B g))
    (@♭ dC : (@♭ g : G) → Discrete (C g)) (@♭ C-set : (g : G) → IsSet (C g))
    (@♭ f : (g : G) → C g → B g)
    (@♭ A : Σ G B → Set ℓ)
    (@♭ KB : Closed (Σ (Σ G B) A))
    (@♭ KC : Closed (Σ (Σ G C) (A ∘ (λ w → fst w , f (fst w) (snd w)))))
    where

    -- The payloads as ATOMS, as in the closed form.
    abstract
      payloadB : Closed (Σ (Σ G B) A)
      payloadB = KB

      payloadC : Closed (Σ (Σ G C) (A ∘ (λ w → fst w , f (fst w) (snd w))))
      payloadC = KC

      payloadB-path : payloadB ≡ KB
      payloadB-path = refl

      payloadC-path : payloadC ≡ KC
      payloadC-path = refl

      -- The decision procedure of the context, as an opaque copy too.
      -- The derivation is generic in the supplied decider
      -- (DecidableBase.Fibre branches on it; it also enters the sethood
      -- of G and the local fibre types), and with the copy a client does
      -- not have to normalise it at its points. The native input
      -- families and assumptions are unchanged.
      decision : DecEq G
      decision = dec

    -- Whole data: terminal shape data of the two whole total sources.
    wholeB : ShapeData (Σ (Σ G B) A)
    wholeB = closed-bridge fe (Σ (Σ G B) A) payloadB

    wholeC : ShapeData (Σ (Σ G C) (A ∘ (λ w → fst w , f (fst w) (snd w))))
    wholeC = closed-bridge fe
      (Σ (Σ G C) (A ∘ (λ w → fst w , f (fst w) (snd w)))) payloadC

    module Specialised =
      Specialise fe {dG = dG} decision dB B-set dC C-set f A wholeB wholeC

    -- The WHOLE diagram over Σ G C → Σ G B: its bases, its two relative
    -- reflections, its canonical comparison. Exported by renaming, so
    -- that every user spells them in one way. Kernel is about this
    -- global diagram, never about a local one.
    open Specialised.OnB public using ()
      renaming (whole to whole-reflB; base-discrete to wholeB-discrete;
                base-set to wholeB-set)
    open Specialised.OnC public using ()
      renaming (whole to whole-reflC; base-discrete to wholeC-discrete;
                base-set to wholeC-set)
    open Specialised public using (module Whole)

    Kernel : Set ℓ
    Kernel = Whole.TotalComparisonIsEquivalence

    whole-from-kernel : Kernel → Whole.ComparisonIsEquivalence
    whole-from-kernel = Whole.FromTotal.fibres wholeC-set

    -- Kernel from the same statement about other reflections MB, MC of
    -- the whole diagram: Supplied is their comparison.
    module KernelFrom
      (@♭ MB : RelativeShapeOver (Σ G B) wholeB-discrete A)
      (@♭ MC : RelativeShapeOver (Σ G C) wholeC-discrete
                 (A ∘ (λ w → fst w , f (fst w) (snd w)))) where

      module ToWhole = Independence fe (Σ G B) (Σ G C) wholeB-discrete
        wholeC-discrete A (λ w → fst w , f (fst w) (snd w))
        MB whole-reflB MC whole-reflC
      open ToWhole public using () renaming (module TK to Supplied)

      kernel : Supplied.TotalComparisonIsEquivalence → Kernel
      kernel = ToWhole.Transfer.total

    module At (@♭ g₀ : G) where

      -- B9 at g₀ (ContextSpecialisation): the restricted reflections, the
      -- comparisons along the inclusions of the fibres of the context,
      -- the whole/local square and the passage from Kernel to the local
      -- diagram. Its own module Local is a second instance of Raw below,
      -- with the same arguments.
      module Point = Specialised.AtPoint g₀

      -- Raw outputs: the whole reflections restricted to the fibre of the
      -- context over g₀, and the terminal data of the two local total
      -- sources that carry them.
      open Point.PB public using ()
        renaming (restricted to raw-reflB; local-data to raw-dataB)
      open Point.PC public using ()
        renaming (restricted to raw-reflC; local-data to raw-dataC)

      -- Default outputs.
      reflB : RelativeShapeOver (B g₀) (dB g₀) (A ∘ (λ b → g₀ , b))
      reflB = sealed raw-reflB

      reflC : RelativeShapeOver (C g₀) (dC g₀) (A ∘ (λ b → g₀ , b) ∘ f g₀)
      reflC = sealed raw-reflC

      reflB-path : reflB ≡ raw-reflB
      reflB-path = sealed-path raw-reflB

      reflC-path : reflC ≡ raw-reflC
      reflC-path = sealed-path raw-reflC

      -- ONE instance of the comparison machinery for the pair (raw,
      -- default), as in the closed form. Raw is the LOCAL diagram for the
      -- raw outputs; it does not replace the global Whole.
      module Sealing = Independence fe (B g₀) (C g₀) (dB g₀) (dC g₀)
        (A ∘ (λ b → g₀ , b)) (f g₀) raw-reflB reflB raw-reflC reflC
      open Sealing public using ()
        renaming (module TK to Raw; module TL to Diagram;
                  module C′ to TotalBridgeC; module FC to BridgeB)

      module BridgeC = ShapeChoice.FiberChoice fe raw-reflC reflC

      -- The square of the two LOCAL comparisons with the bridges is
      -- Sealing.natural. Sealing.pull is the B-side bridge in each fibre.
      pull-is : (w : Raw.PulledTotal)
              → Sealing.pull w
                ≡ (fst w , BridgeB.forward (f g₀ (fst w)) (snd w))
      pull-is w = refl

      -- The comparisons along the inclusions  b ↦ (g₀ , b),  c ↦ (g₀ , c)
      -- (equivalences, by DecidableRestriction), and the square
      --   InclusionB.comparison (f g₀ c) (local comparison of w)
      --     ≡ Whole.comparison (g₀ , c) (InclusionC.comparison c w)
      -- for ORDINARY c and w, in the names of ContextSpecialisation.
      module InclusionB = Point.PB.Inclusion
      module InclusionC = Point.PC.Inclusion
      open Point public using (square)

      raw-from-kernel : Kernel → Raw.ComparisonIsEquivalence
      raw-from-kernel = Point.fibres

      from-kernel : Kernel → Diagram.ComparisonIsEquivalence
      from-kernel k = Sealing.fibre-form (C-set g₀) (raw-from-kernel k)

      total-from-kernel : Kernel → Diagram.TotalComparisonIsEquivalence
      total-from-kernel k = Diagram.FromFibres.total (from-kernel k)

      decidable : (@♭ decB : DecEq (B g₀)) (@♭ decC : DecEq (C g₀))
                → Diagram.ComparisonIsEquivalence
      decidable decB decC = Stable.fibres fe (B g₀) (C g₀) (dB g₀) (dC g₀)
        decB decC (A ∘ (λ b → g₀ , b)) (f g₀) reflB reflC

      -- Any other local reflections of the same diagram.
      module ForPayloads
        (@♭ MB : RelativeShapeOver (B g₀) (dB g₀) (A ∘ (λ b → g₀ , b)))
        (@♭ MC : RelativeShapeOver (C g₀) (dC g₀) (A ∘ (λ b → g₀ , b) ∘ f g₀))
        where

        module FromRaw = Independence fe (B g₀) (C g₀) (dB g₀) (dC g₀)
          (A ∘ (λ b → g₀ , b)) (f g₀) raw-reflB MB raw-reflC MC
        open FromRaw public using () renaming (module TL to Chosen)

        from-kernel′ : Kernel → Chosen.ComparisonIsEquivalence
        from-kernel′ k = FromRaw.fibre-form (C-set g₀) (raw-from-kernel k)

        total-from-kernel′ : Kernel → Chosen.TotalComparisonIsEquivalence
        total-from-kernel′ k = Chosen.FromFibres.total (from-kernel′ k)

  ----------------------------------------------------------------------
  -- The same over a decidable context, from terminal shape data of the
  -- two whole total sources, however obtained (step S3a, the library half
  -- of the direct in-module route; DIRECT-OPEN-DIAGRAM-ROUTE-01,
  -- FABLE-REVIEW-06 section 4.4).
  --
  -- Open takes CLOSED PAYLOADS of the whole totals and bridges them.
  -- A diagram assembled inside a module has no closed payload of its
  -- whole totals: it has two CONTEXTUAL captures, from which TotalBridge
  -- and GlobalChoice.Along derive terminal shape data of the whole totals
  -- (DiagramBundle.AssembleCaptured). Such data are not Closed payloads
  -- and are not passed off as such. OpenData takes the two ShapeData as
  -- its arguments WB, WC and, from there on, is Open word for word:
  -- after the definitions of wholeB and wholeC, Open never uses that they
  -- came from closed-bridge.
  --
  -- Opaque copies, as in Open and for the same observed reason: here the
  -- copies are of the supplied ShapeData themselves,
  --   wholeB, wholeC              do not unfold outside the block
  --   wholeB-path, wholeC-path    wholeB ≡ WB, wholeC ≡ WC
  -- and of the decision procedure. Every output is derived from the
  -- copies; none reduces by definition to a carrier or unit of WB, WC or
  -- of whatever they were derived from. The abstract block introduces
  -- definitions and no axiom.
  --
  -- Output: the names of Open, with the same meaning. Kernel is GLOBAL,
  -- about the whole diagram for the reflections derived from the copies,
  -- and an ORDINARY hypothesis wherever it occurs.

  module OpenData
    (@♭ fe : FunExtAt ℓ)
    {@♭ G : Set ℓ} {@♭ dG : Discrete G} (@♭ dec : DecEq G)
    {@♭ B C : G → Set ℓ}
    (@♭ dB : (@♭ g : G) → Discrete (B g)) (@♭ B-set : (g : G) → IsSet (B g))
    (@♭ dC : (@♭ g : G) → Discrete (C g)) (@♭ C-set : (g : G) → IsSet (C g))
    (@♭ f : (g : G) → C g → B g)
    (@♭ A : Σ G B → Set ℓ)
    (@♭ WB : ShapeData (Σ (Σ G B) A))
    (@♭ WC : ShapeData (Σ (Σ G C) (A ∘ (λ w → fst w , f (fst w) (snd w)))))
    where

    abstract
      wholeB : ShapeData (Σ (Σ G B) A)
      wholeB = WB

      wholeC : ShapeData (Σ (Σ G C) (A ∘ (λ w → fst w , f (fst w) (snd w))))
      wholeC = WC

      wholeB-path : wholeB ≡ WB
      wholeB-path = refl

      wholeC-path : wholeC ≡ WC
      wholeC-path = refl

      decision : DecEq G
      decision = dec

    module Specialised =
      Specialise fe {dG = dG} decision dB B-set dC C-set f A wholeB wholeC

    -- The WHOLE diagram over Σ G C → Σ G B: its bases, its two relative
    -- reflections, its canonical comparison. Exported by renaming, so
    -- that every user spells them in one way. Kernel is about this
    -- global diagram, never about a local one.
    open Specialised.OnB public using ()
      renaming (whole to whole-reflB; base-discrete to wholeB-discrete;
                base-set to wholeB-set)
    open Specialised.OnC public using ()
      renaming (whole to whole-reflC; base-discrete to wholeC-discrete;
                base-set to wholeC-set)
    open Specialised public using (module Whole)

    Kernel : Set ℓ
    Kernel = Whole.TotalComparisonIsEquivalence

    whole-from-kernel : Kernel → Whole.ComparisonIsEquivalence
    whole-from-kernel = Whole.FromTotal.fibres wholeC-set

    -- Kernel from the same statement about other reflections MB, MC of
    -- the whole diagram: Supplied is their comparison.
    module KernelFrom
      (@♭ MB : RelativeShapeOver (Σ G B) wholeB-discrete A)
      (@♭ MC : RelativeShapeOver (Σ G C) wholeC-discrete
                 (A ∘ (λ w → fst w , f (fst w) (snd w)))) where

      module ToWhole = Independence fe (Σ G B) (Σ G C) wholeB-discrete
        wholeC-discrete A (λ w → fst w , f (fst w) (snd w))
        MB whole-reflB MC whole-reflC
      open ToWhole public using () renaming (module TK to Supplied)

      kernel : Supplied.TotalComparisonIsEquivalence → Kernel
      kernel = ToWhole.Transfer.total

    module At (@♭ g₀ : G) where

      -- B9 at g₀ (ContextSpecialisation): the restricted reflections, the
      -- comparisons along the inclusions of the fibres of the context,
      -- the whole/local square and the passage from Kernel to the local
      -- diagram. Its own module Local is a second instance of Raw below,
      -- with the same arguments.
      module Point = Specialised.AtPoint g₀

      -- Raw outputs: the whole reflections restricted to the fibre of the
      -- context over g₀, and the terminal data of the two local total
      -- sources that carry them.
      open Point.PB public using ()
        renaming (restricted to raw-reflB; local-data to raw-dataB)
      open Point.PC public using ()
        renaming (restricted to raw-reflC; local-data to raw-dataC)

      -- Default outputs.
      reflB : RelativeShapeOver (B g₀) (dB g₀) (A ∘ (λ b → g₀ , b))
      reflB = sealed raw-reflB

      reflC : RelativeShapeOver (C g₀) (dC g₀) (A ∘ (λ b → g₀ , b) ∘ f g₀)
      reflC = sealed raw-reflC

      reflB-path : reflB ≡ raw-reflB
      reflB-path = sealed-path raw-reflB

      reflC-path : reflC ≡ raw-reflC
      reflC-path = sealed-path raw-reflC

      -- ONE instance of the comparison machinery for the pair (raw,
      -- default), as in the closed form. Raw is the LOCAL diagram for the
      -- raw outputs; it does not replace the global Whole.
      module Sealing = Independence fe (B g₀) (C g₀) (dB g₀) (dC g₀)
        (A ∘ (λ b → g₀ , b)) (f g₀) raw-reflB reflB raw-reflC reflC
      open Sealing public using ()
        renaming (module TK to Raw; module TL to Diagram;
                  module C′ to TotalBridgeC; module FC to BridgeB)

      module BridgeC = ShapeChoice.FiberChoice fe raw-reflC reflC

      -- The square of the two LOCAL comparisons with the bridges is
      -- Sealing.natural. Sealing.pull is the B-side bridge in each fibre.
      pull-is : (w : Raw.PulledTotal)
              → Sealing.pull w
                ≡ (fst w , BridgeB.forward (f g₀ (fst w)) (snd w))
      pull-is w = refl

      -- The comparisons along the inclusions  b ↦ (g₀ , b),  c ↦ (g₀ , c)
      -- (equivalences, by DecidableRestriction), and the square
      --   InclusionB.comparison (f g₀ c) (local comparison of w)
      --     ≡ Whole.comparison (g₀ , c) (InclusionC.comparison c w)
      -- for ORDINARY c and w, in the names of ContextSpecialisation.
      module InclusionB = Point.PB.Inclusion
      module InclusionC = Point.PC.Inclusion
      open Point public using (square)

      raw-from-kernel : Kernel → Raw.ComparisonIsEquivalence
      raw-from-kernel = Point.fibres

      from-kernel : Kernel → Diagram.ComparisonIsEquivalence
      from-kernel k = Sealing.fibre-form (C-set g₀) (raw-from-kernel k)

      total-from-kernel : Kernel → Diagram.TotalComparisonIsEquivalence
      total-from-kernel k = Diagram.FromFibres.total (from-kernel k)

      decidable : (@♭ decB : DecEq (B g₀)) (@♭ decC : DecEq (C g₀))
                → Diagram.ComparisonIsEquivalence
      decidable decB decC = Stable.fibres fe (B g₀) (C g₀) (dB g₀) (dC g₀)
        decB decC (A ∘ (λ b → g₀ , b)) (f g₀) reflB reflC

      -- Any other local reflections of the same diagram.
      module ForPayloads
        (@♭ MB : RelativeShapeOver (B g₀) (dB g₀) (A ∘ (λ b → g₀ , b)))
        (@♭ MC : RelativeShapeOver (C g₀) (dC g₀) (A ∘ (λ b → g₀ , b) ∘ f g₀))
        where

        module FromRaw = Independence fe (B g₀) (C g₀) (dB g₀) (dC g₀)
          (A ∘ (λ b → g₀ , b)) (f g₀) raw-reflB MB raw-reflC MC
        open FromRaw public using () renaming (module TL to Chosen)

        from-kernel′ : Kernel → Chosen.ComparisonIsEquivalence
        from-kernel′ k = FromRaw.fibre-form (C-set g₀) (raw-from-kernel k)

        total-from-kernel′ : Kernel → Chosen.TotalComparisonIsEquivalence
        total-from-kernel′ k = Chosen.FromFibres.total (from-kernel′ k)

  ----------------------------------------------------------------------
  -- From a fresh capture to a local reflection.
  --
  -- ForPayloads takes relative reflections. A capture made in an open
  -- module is a CapturedShape: a relative reflection over its own packed
  -- context together with a point. When that context has decidable
  -- equality, DecidableBase.CaptureFibre gives terminal shape data of the
  -- captured source, and when the source is a total space Σ B₀ A₀ over a
  -- discrete set, TotalConverse gives the relative reflection over B₀.
  -- This module is those two existing steps under one name, with the same
  -- policy as above:
  --   raw-reflection   the derived reflection. Its total carrier and its
  --                    unit ARE those of the capture, by definition (the
  --                    payload of a capture is not replaced by an atom
  --                    here: that identity is the point of this output).
  --   reflection       the default: the raw one sealed, for statements in
  --                    a client's own terms.
  -- Both are valid choices for the local diagram; neither is the choice
  -- made by Open.At. ForPayloads compares them with it canonically.

  module FromCapture
    (@♭ fe : FunExtAt ℓ)
    {@♭ B₀ : Set ℓ} (@♭ dB₀ : Discrete B₀) (@♭ B₀-set : IsSet B₀)
    {@♭ A₀ : B₀ → Set ℓ}
    (@♭ s : CapturedShape {ℓ = ℓ} (Σ B₀ A₀))
    (@♭ dec : DecEq (C.Output.context s)) where

    local-data : ShapeData (Σ B₀ A₀)
    local-data = CaptureFibre.capture-data fe s dec

    raw-reflection : RelativeShapeOver B₀ dB₀ A₀
    raw-reflection = Converse.relative fe {dΓ = dB₀} B₀-set local-data

    reflection : RelativeShapeOver B₀ dB₀ A₀
    reflection = sealed raw-reflection

    reflection-path : reflection ≡ raw-reflection
    reflection-path = sealed-path raw-reflection

    module Bridge = ShapeChoice.FiberChoice fe raw-reflection reflection
