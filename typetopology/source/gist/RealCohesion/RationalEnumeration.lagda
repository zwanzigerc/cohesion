Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 10 November 2026. See the AI disclosure in
gist.RealCohesion.index.

An enumeration of the rationals, and rational witnesses chosen as
functions of the data.

The proofs in Fable's note on Axiom T in Shulman's §§11 and 12 [1]
define sequences of rationals by least-witness search over a fixed
enumeration of ℚ, so that no choice principle is needed. We enumerate
ℚ with TypeTopology's pairing ℕ × ℕ ≃ ℕ (Naturals.Binary). The number
pair (pair (s , k) , d) stands for the fraction k / (d + 1) if s is 0
and for -(k + 1) / (d + 1) otherwise, and toℚ reduces it to lowest
terms. A rational is the reduction of its own fraction (toℚ-to𝔽), so
the enumeration is surjective, with an explicit preimage.

If a decidable property of rationals merely holds of some rational,
TypeTopology's exit truncations (Naturals.ExitTruncation) give the
least index at which the enumeration satisfies it. This least witness
is unique, so it is a function of the data. Only its property is
used, so we make it abstract: otherwise Agda may unfold the search
when it compares two terms that denote the same witness.

[1] Fable. Shulman's stated questions: three updates, Part A.
    Working note, 10 November 2026, audited by GPT-6 Astra.
    references/F18-shulman-three-updates.md

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.PropTrunc

module gist.RealCohesion.RationalEnumeration
        (pt : propositional-truncations-exist)
       where

open import Naturals.Binary using (pair ; riap ; riap-pair)
open import Naturals.ExitTruncation
open import Integers.Type
open import Rationals.Fractions
open import Rationals.Type

open PropositionalTruncation pt
open exit-truncations pt

\end{code}

The enumeration.

\begin{code}

signed-numeral : ℕ × ℕ → ℤ
signed-numeral (0      , k) = pos k
signed-numeral (succ _ , k) = negsucc k

numerator-code : ℤ → ℕ
numerator-code (pos k)     = pair (0 , k)
numerator-code (negsucc k) = pair (1 , k)

signed-numeral-of-code : (x : ℤ) → signed-numeral (riap (numerator-code x)) ＝ x
signed-numeral-of-code (pos k)     = ap signed-numeral (riap-pair (0 , k))
signed-numeral-of-code (negsucc k) = ap signed-numeral (riap-pair (1 , k))

ℚ-enumeration : ℕ → ℚ
ℚ-enumeration n = toℚ (signed-numeral (riap (pr₁ (riap n))) , pr₂ (riap n))

ℚ-enumeration-is-surjective : (q : ℚ) → Σ n ꞉ ℕ , ℚ-enumeration n ＝ q
ℚ-enumeration-is-surjective ((x , d) , α) = pair (numerator-code x , d) , γ
 where
  γ : ℚ-enumeration (pair (numerator-code x , d)) ＝ ((x , d) , α)
  γ = ap (λ (m , e) → toℚ (signed-numeral (riap m) , e))
         (riap-pair (numerator-code x , d))
    ∙ ap (λ - → toℚ (- , d)) (signed-numeral-of-code x)
    ∙ toℚ-to𝔽 ((x , d) , α) ⁻¹

\end{code}

Rational witnesses of decidable properties, as functions of the data.

\begin{code}

module _ {𝓦 : Universe}
         (P : ℚ → 𝓦 ̇ )
         (δ : (q : ℚ) → is-decidable (P q))
       where

 least-enumerated-witness : (∃ q ꞉ ℚ , P q) → Σ n ꞉ ℕ , P (ℚ-enumeration n)
 least-enumerated-witness w =
  exit-truncation (P ∘ ℚ-enumeration) (δ ∘ ℚ-enumeration) (∥∥-functor γ w)
  where
   γ : (Σ q ꞉ ℚ , P q) → Σ n ꞉ ℕ , P (ℚ-enumeration n)
   γ (q , p) = pr₁ (ℚ-enumeration-is-surjective q) ,
               transport P (pr₂ (ℚ-enumeration-is-surjective q) ⁻¹) p

 abstract
  rational-witness : (∃ q ꞉ ℚ , P q) → ℚ
  rational-witness w = ℚ-enumeration (pr₁ (least-enumerated-witness w))

  rational-witness-property : (w : ∃ q ꞉ ℚ , P q) → P (rational-witness w)
  rational-witness-property w = pr₂ (least-enumerated-witness w)

\end{code}
