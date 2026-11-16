Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 26 October 2026. See the AI disclosure in
gist.RealCohesion.index.

An abstract copy of the embedding of the rationals in the reals.

The embedding ι : ℚ → ℝ of DedekindReals.Type builds a real number
together with proofs of the cut axioms, which use the density of the
rationals and other lemmas that compute with normal forms of
fractions. When Agda compares ι x with ι y for rationals x and y that
are equal only after some computation, for instance ♭-counit (x ^♭)
and x, it may unfold ι and these proofs before it reduces x and y,
and type checking then takes an extremely long time. The function ιₐ
below is equal to ι, but it is abstract, so Agda compares ιₐ x and ιₐ y
by comparing x and y. We use ιₐ in the analytic modules, and convert
to ι when stating results.

Similarly, 0ℝₐ is an abstract copy of 0ℝ = ι 0. We use it in the types
of the fields of records: Agda normalizes these types when it checks a
record declaration, and the normal form of 0ℝ is too large for this.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.RationalPoints
        (fe : Fun-Ext)
        (pe : Prop-Ext)
        (pt : propositional-truncations-exist)
       where

open import Notation.CanonicalMap
open import Notation.Order
open import Rationals.Order
open import Rationals.Type
open import DedekindReals.Type fe pe pt

abstract
 ιₐ : ℚ → ℝ
 ιₐ = ι

 ιₐ-is-ι : (x : ℚ) → ιₐ x ＝ ι x
 ιₐ-is-ι x = refl

 ιₐ-lower : (r x : ℚ) → r < x → r < ιₐ x
 ιₐ-lower r x l = l

 ιₐ-lower⁻¹ : (r x : ℚ) → r < ιₐ x → r < x
 ιₐ-lower⁻¹ r x l = l

 ιₐ-upper : (x r : ℚ) → x < r → ιₐ x < r
 ιₐ-upper x r l = l

 ιₐ-upper⁻¹ : (x r : ℚ) → ιₐ x < r → x < r
 ιₐ-upper⁻¹ x r l = l

 0ℝₐ : ℝ
 0ℝₐ = 0ℝ

 0ℝₐ-is-0ℝ : 0ℝₐ ＝ 0ℝ
 0ℝₐ-is-0ℝ = refl

\end{code}
