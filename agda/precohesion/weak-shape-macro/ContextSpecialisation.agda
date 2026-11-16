{-# OPTIONS --cohesion --without-K --flat-split #-}

-- From a whole diagram over a decidable context to the diagram at the
-- current point: field B9 of FABLE-REVIEW-05 section 4. Postulate-free.
-- Claude (Fable), 13 November 2026; fable-impl-10. HANDOFF-17 section 3,
-- FABLE05-ASSEMBLY-REVIEW-01 section 3, B9-NATIVE-ASSEMBLY-READINESS-01.
--
-- THE DIAGRAM. All data crisp, at one level ℓ:
--   G                a discrete type with DECIDABLE equality: the packed
--                    context of an open module
--   B, C : G → Set   families of discrete SETS: the local bases. Nothing
--                    is assumed about their equality.
--   f : (g : G) → C g → B g      the local base maps
--   A : Σ G B → Set              the source family, with ARBITRARY fibres
--   sB, sC           terminal shape data of the two whole total sources
--                      Σ (Σ G B) A    and    Σ (Σ G C) (A ∘ total-map)
--                    where total-map (g , c) = (g , f g c).
-- The whole diagram is the reindexing of A along total-map, between the
-- discrete sets Σ G C and Σ G B: a CLOSED diagram of the kind the main
-- theorem is about, to which no decidability hypothesis applies.
-- (In the code total-map and the inclusions of the fibres are written as
-- lambdas at every use:  λ w → fst w , f (fst w) (snd w)  and
-- λ c → g₀ , c.  DecidableRestriction explains why they have no names.)
--
-- WHAT IS DERIVED. First, for ARBITRARY reflections at the four corners
-- (module Square): the square below and two-out-of-three along it; this
-- part uses nothing about a decidable context. Then, at a crisp point g₀
-- of a decidable context (module Specialise):
--   AtPoint.PB.restricted, PC.restricted
--                    the local relative reflections over B g₀ and C g₀,
--                    carried by the fibres over g₀ of the two whole
--                    shapes (DecidableRestriction)
--   AtPoint.Local    the ACTUAL canonical comparison of ShapeReindexing
--                    for the local diagram  f g₀ : C g₀ → B g₀,  with its
--                    unit law Local.comparison-on-unit
--   AtPoint.square   for c : C g₀ and w in the local fibre over c,
--                        include_B (local comparison of w)
--                          ≡ whole comparison at (g₀ , c) of include_C w
--                    where include_B, include_C are the canonical
--                    comparisons along the inclusions of the fibres of the
--                    context (equivalences, by DecidableRestriction). The
--                    point c is ORDINARY.
--   AtPoint.fibres, AtPoint.total
--                    if the comparison of the WHOLE diagram is an
--                    equivalence (total form), so is the local comparison,
--                    in every fibre and in total form
--   AtPoint.ForPayloads.fibres′
--                    the same for any other pair of local relative
--                    reflections of the same local diagram, for instance
--                    those of fresh captures at the current point
--                    (ReindexingChoice)
--
-- HOW. The square of base maps
--        C g₀ ──f g₀──▶ B g₀
--         │include       │include
--         ▼              ▼
--       Σ G C ─total-map▶ Σ G B
-- commutes on the nose, so the two composites have ONE canonical
-- comparison. The pasting law (ReindexingComposition) factors it in two
-- ways; `square` is the equation of the two factorisations. It is proved
-- from the uniqueness half of the local reflection over C g₀, a statement
-- about whole maps over C g₀: no fibre over an ordinary point c is treated
-- as a terminal reflection, and nothing is decided about C g₀ or B g₀.
-- Invertibility is then moved along the square: two-out-of-three, with the
-- supplied hypothesis and the two inclusion comparisons.
--
-- WHAT THIS IS NOT. The hypothesis `kernel` is the conclusion of the
-- local-connectedness theorem for the whole diagram. It is NOT proved
-- here, and this module does not say that continuity implies it. Taking
-- the fibre over g₀ of a comparison that is already an equivalence is
-- native reasoning about pullbacks; it is not an assertion that shape
-- commutes with the pullback along total-map. Decidability is used for G
-- only, through DecidableBase.Fibre.
module ContextSpecialisation where

open import Foundations
open import RelativeSliceShape
open import ShapeChoice using (FunExtAt)
open import GlobalPrecohesion
open import DecidableBase using (DecEq)
open import DecidableRestriction using (module Restrict)
open import ReindexingAssembly using (module TotalForm)
open import ReindexingComposition using (module Pasting)
open import ReindexingChoice using (module Independence)

module _ {@♭ ℓ : Level} where

  ----------------------------------------------------------------------
  -- The square, for ARBITRARY reflections at its four corners. Nothing
  -- about a decidable context is used here: this part is the pasting law
  -- twice. It is stated for abstract reflections so that its proof is
  -- checked without unfolding any derived one.

  module Square
    (@♭ fe : FunExtAt ℓ)
    {@♭ G : Set ℓ} {@♭ B C : G → Set ℓ}
    (@♭ dB̂ : Discrete (Σ G B)) (@♭ dĈ : Discrete (Σ G C))
    (@♭ f : (g : G) → C g → B g)
    (@♭ A : Σ G B → Set ℓ)
    (@♭ g₀ : G)
    (@♭ dB₀ : Discrete (B g₀)) (@♭ dC₀ : Discrete (C g₀))
    (@♭ KB : RelativeShapeOver (Σ G B) dB̂ A)
    (@♭ KC : RelativeShapeOver (Σ G C) dĈ (A ∘ (λ w → fst w , f (fst w) (snd w))))
    (@♭ LB : RelativeShapeOver (B g₀) dB₀ (A ∘ (λ b → g₀ , b)))
    (@♭ LC : RelativeShapeOver (C g₀) dC₀ (A ∘ (λ w → fst w , f (fst w) (snd w)) ∘ (λ c → g₀ , c)))
    where

    -- The four canonical comparisons.
    module Whole = TotalForm (Σ G B) (Σ G C) dB̂ dĈ A (λ w → fst w , f (fst w) (snd w)) KB KC
    module InB = TotalForm (Σ G B) (B g₀) dB̂ dB₀ A (λ b → g₀ , b) KB LB
    module InC = TotalForm (Σ G C) (C g₀) dĈ dC₀ (A ∘ (λ w → fst w , f (fst w) (snd w)))
      (λ c → g₀ , c) KC LC
    module Local = TotalForm (B g₀) (C g₀) dB₀ dC₀ (A ∘ (λ b → g₀ , b)) (f g₀)
      LB LC

    private
      -- total-map ∘ inclusion: first the inclusion, then the whole map.
      module First = Pasting fe (Σ G B) (Σ G C) (C g₀) dB̂ dĈ dC₀
        A (λ w → fst w , f (fst w) (snd w)) (λ c → g₀ , c) KB KC LC

      -- inclusion ∘ f g₀: first the local map, then the inclusion. The
      -- same map C g₀ → Σ G B, definitionally.
      module Second = Pasting fe (Σ G B) (B g₀) (C g₀) dB̂ dB₀ dC₀
        A (λ b → g₀ , b) (f g₀) KB LB LC

    -- The local comparison followed by the inclusion on the B side is the
    -- inclusion on the C side followed by the whole comparison at (g₀ , c).
    square : (c : C g₀) (w : Output.family LC c)
           → InB.comparison (f g₀ c) (Local.comparison c w)
             ≡ Whole.comparison (g₀ , c) (InC.comparison c w)
    square c w = sym (Second.fibrewise c w) ∙ First.fibrewise c w

    -- Two-out-of-three along the square. All evidence is ordinary.
    fibres : InB.ComparisonIsEquivalence → InC.ComparisonIsEquivalence
           → Whole.ComparisonIsEquivalence → Local.ComparisonIsEquivalence
    fibres inB inC whole = Second.cancel-fibres inB
      (First.compose-fibres whole inC)

  ----------------------------------------------------------------------
  -- The decidable context.

  module Specialise
    (@♭ fe : FunExtAt ℓ)
    {@♭ G : Set ℓ} {@♭ dG : Discrete G} (@♭ dec : DecEq G)
    {@♭ B C : G → Set ℓ}
    (@♭ dB : (@♭ g : G) → Discrete (B g)) (@♭ B-set : (g : G) → IsSet (B g))
    (@♭ dC : (@♭ g : G) → Discrete (C g)) (@♭ C-set : (g : G) → IsSet (C g))
    (@♭ f : (g : G) → C g → B g)
    (@♭ A : Σ G B → Set ℓ)
    (@♭ sB : ShapeData (Σ (Σ G B) A))
    (@♭ sC : ShapeData (Σ (Σ G C) (A ∘ (λ w → fst w , f (fst w) (snd w)))))
    where

    module OnB = Restrict fe {dG = dG} dec dB B-set {A = A} sB
    module OnC = Restrict fe {dG = dG} dec dC C-set {A = A ∘ (λ w → fst w , f (fst w) (snd w))} sC

    -- The whole diagram: its two relative reflections and their canonical
    -- comparison.
    module Whole = TotalForm (Σ G B) (Σ G C)
      OnB.base-discrete OnC.base-discrete A (λ w → fst w , f (fst w) (snd w)) OnB.whole OnC.whole

    module AtPoint (@♭ g₀ : G) where

      module PB = OnB.AtPoint g₀
      module PC = OnC.AtPoint g₀

      private
        module Sq = Square fe OnB.base-discrete OnC.base-discrete f A g₀
          (dB g₀) (dC g₀) OnB.whole OnC.whole PB.restricted PC.restricted

      -- The local diagram  f g₀ : C g₀ → B g₀  with the restricted
      -- reflections, its canonical comparison (Local.comparison), the unit
      -- law (Local.comparison-on-unit), and the square.
      open Sq public using (module Local; square)

      -- B9. The supplied conclusion for the whole diagram gives the
      -- conclusion for the local diagram at the current point.
      fibres : Whole.TotalComparisonIsEquivalence → Local.ComparisonIsEquivalence
      fibres kernel = Sq.fibres PB.inclusion-fibres PC.inclusion-fibres
        (Whole.FromTotal.fibres OnC.base-set kernel)

      total : Whole.TotalComparisonIsEquivalence
            → Local.TotalComparisonIsEquivalence
      total kernel = Local.FromFibres.total (fibres kernel)

      -- The same for any other local reflections of the same diagram.
      module ForPayloads
        (@♭ MB : RelativeShapeOver (B g₀) (dB g₀) (A ∘ (λ b → g₀ , b)))
        (@♭ MC : RelativeShapeOver (C g₀) (dC g₀) (A ∘ (λ b → g₀ , b) ∘ f g₀))
        where

        module Chosen = TotalForm (B g₀) (C g₀) (dB g₀) (dC g₀)
          (A ∘ (λ b → g₀ , b)) (f g₀) MB MC

        private
          module I = Independence fe (B g₀) (C g₀) (dB g₀) (dC g₀)
            (A ∘ (λ b → g₀ , b)) (f g₀) PB.restricted MB PC.restricted MC

        fibres′ : Whole.TotalComparisonIsEquivalence
                → Chosen.ComparisonIsEquivalence
        fibres′ kernel = I.fibre-form (C-set g₀) (fibres kernel)

        -- The comparison of the chosen reflections and that of the
        -- restricted ones differ by the canonical comparisons of the
        -- choices: ReindexingChoice.Independence.natural.
        open I public using (natural)
