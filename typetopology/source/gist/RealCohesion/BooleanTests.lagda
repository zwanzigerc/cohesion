Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 13 November 2026 (local time), in the consolidation that
followed the final audits: step K4 of Claude Fable 5.2's plan [1], as
corrected by its addendum [2] and released by GPT-6 Astra [3]. See the
AI disclosure in gist.RealCohesion.index.

The Boolean test
----------------

If every map from a pointed type B to 𝟚 is constant, then so is every
map from B to a type X with decidable equality: a map h : B → X is
compared with its value at the point by the map to 𝟚 that decides the
comparison.

This uses no modality, no function extensionality and no parameter.
It is the common core of three statements that used to prove it
separately:

 * discrete-types-are-null in gist.Orbifolds.Nullification, for any
   pointed generator;

 * discrete-types-are-ℝ-null in gist.RealCohesion.DiscreteSets, for ℝ
   pointed by 0;

 * types-with-decidable-equality-are-♭-discrete in
   gist.Orbifolds.C1Discreteness, under Axiom C1, which tested with
   maps into ℕ; it now uses 𝟚 through gist.RealCohesion.PunctualCohesion.

Source. The code is the local γ of discrete-types-are-null in
gist.Orbifolds.Nullification of the frozen delivery r3 (lines 202–218),
by Claude Opus 5.5, with the map and the point at which it is tested
made arguments of the lemma, as in Claude Fable 5.2's scratch check
BooleanTestsCheck.lagda (SHA-256 b912c2b8…, in the companion of [2]),
whose code is used here unchanged, apart from the module name.

[1] Claude Fable 5.2. Plan: consolidation of r3, and "C1 + NC in place
    of R♭" (G27(d)), 13 November 2026, step K4.
    references/F02-consolidation-plan.md

[2] Claude Fable 5.2. Addendum 01 to the consolidation plan,
    13 November 2026, Section 1.
    references/F03-consolidation-plan-addendum-01.md

[3] GPT-6 Astra. Consolidation implementation, second release,
    13 November 2026.
    references/A27-consolidation-release-02.txt

\begin{code}

{-# OPTIONS --safe --without-K #-}

module gist.RealCohesion.BooleanTests where

open import MLTT.Spartan
open import MLTT.Two-Properties using (zero-is-not-one)
open import UF.DiscreteAndSeparated using (is-discrete)

maps-into-types-with-decidable-equality-are-constant
 : {𝓤 𝓦 : Universe} (B : 𝓤 ̇ ) (b : B)
 → ((f : B → 𝟚) (v : B) → f v ＝ f b)
 → (X : 𝓦 ̇ ) → is-discrete X → (h : B → X) (v : B) → h v ＝ h b
maps-into-types-with-decidable-equality-are-constant B b c X d h v =
 δ (d (h v) (h b)) (c f v ∙ κ (d (h b) (h b)))
 where
  χ : {x y : X} → is-decidable (x ＝ y) → 𝟚
  χ (inl _) = ₁
  χ (inr _) = ₀

  f : B → 𝟚
  f u = χ (d (h u) (h b))

  κ : (e : is-decidable (h b ＝ h b)) → χ e ＝ ₁
  κ (inl _) = refl
  κ (inr ν) = 𝟘-elim (ν refl)

  δ : (e : is-decidable (h v ＝ h b)) → χ e ＝ ₁ → h v ＝ h b
  δ (inl p) _ = p
  δ (inr _) q = 𝟘-elim (zero-is-not-one q)

\end{code}
