Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 October 2026. See the AI disclosure in
gist.RealCohesion.index.

Boolean values of decisions, and of crisp excluded middle.

For a crisp family U of propositions over a crisp type, crisp excluded
middle decides U at crisp points. We record the resulting Boolean
function and its two characteristic properties, and make it abstract:
nothing should compute with the decisions, and unfolding them can
make type checking very slow. The Boolean value of a decision and its
properties are those of TypeTopology's boolean-value'.

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

module gist.RealCohesion.CrispDecisions where

open import MLTT.Spartan
open import NotionsOfDecidability.DecidableClassifier using (boolean-value')
open import UF.Subsingletons
open import gist.CohesiveApartness.Flat

decide : {𝓦 : Universe} {A : 𝓦 ̇ } → A + ¬ A → 𝟚
decide d = pr₁ (boolean-value' d)

decide-yes : {𝓦 : Universe} {A : 𝓦 ̇ } (d : A + ¬ A) → A → decide d ＝ ₁
decide-yes d = rl-implication (pr₂ (pr₂ (boolean-value' d)))

decide-no : {𝓦 : Universe} {A : 𝓦 ̇ } (d : A + ¬ A) → ¬ A → decide d ＝ ₀
decide-no d = rl-implication (pr₁ (pr₂ (boolean-value' d)))

decide-₁ : {𝓦 : Universe} {A : 𝓦 ̇ } (d : A + ¬ A) → decide d ＝ ₁ → A
decide-₁ d = lr-implication (pr₂ (pr₂ (boolean-value' d)))

decide-₀ : {𝓦 : Universe} {A : 𝓦 ̇ } (d : A + ¬ A) → decide d ＝ ₀ → ¬ A
decide-₀ d = lr-implication (pr₁ (pr₂ (boolean-value' d)))

module _ {@♭ 𝓤 𝓦 : Universe}
         (@♭ cem : Crisp-EM 𝓦)
         {@♭ X : 𝓤 ̇ }
         (@♭ U : X → 𝓦 ̇ )
         (@♭ U-is-prop : (x : X) → is-prop (U x))
       where

 abstract
  crisp-test : (@♭ x : X) → 𝟚
  crisp-test x = decide (cem (U x) (U-is-prop x))

  crisp-test-₁ : (@♭ x : X) → crisp-test x ＝ ₁ → U x
  crisp-test-₁ x = decide-₁ (cem (U x) (U-is-prop x))

  crisp-test-₀ : (@♭ x : X) → crisp-test x ＝ ₀ → ¬ U x
  crisp-test-₀ x = decide-₀ (cem (U x) (U-is-prop x))

  crisp-test-yes : (@♭ x : X) → U x → crisp-test x ＝ ₁
  crisp-test-yes x = decide-yes (cem (U x) (U-is-prop x))

  crisp-test-no : (@♭ x : X) → ¬ U x → crisp-test x ＝ ₀
  crisp-test-no x = decide-no (cem (U x) (U-is-prop x))

\end{code}

Crisp excluded middle for propositions of a smaller universe.

\begin{code}

open import UF.UniverseEmbedding

lifts-of-props-are-props : {𝓤 𝓥 : Universe} {X : 𝓤 ̇ }
                         → is-prop X → is-prop (Lift 𝓥 X)
lifts-of-props-are-props {𝓤} {𝓥} i l l' = ap (lift 𝓥) (i (lower l) (lower l'))

Crisp-EM-lower : {@♭ 𝓤 𝓥 : Universe} → Crisp-EM (𝓤 ⊔ 𝓥) → Crisp-EM 𝓤
Crisp-EM-lower {𝓤} {𝓥} cem P P-is-prop =
 γ (cem (Lift 𝓥 P) (lifts-of-props-are-props P-is-prop))
 where
  γ : Lift 𝓥 P + ¬ Lift 𝓥 P → P + ¬ P
  γ (inl l) = inl (lower l)
  γ (inr ν) = inr (λ p → ν (lift 𝓥 p))

\end{code}
