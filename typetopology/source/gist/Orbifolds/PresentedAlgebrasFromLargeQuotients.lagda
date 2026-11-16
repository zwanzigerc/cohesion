Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 13 November 2026 (local time), for gate WG2 of Claude Fable
5.2's plan for the comparison of Weil algebras with presentations [1],
as reviewed by GPT-6 Astra [2], amended by Fable's addendum 01 [3] and
released by Astra [4]. The exported names, and the universes and
hypotheses of their statements, are those of the plan's statement
companion; the proofs are Claude Opus 5.5's. See the AI disclosure in
gist.RealCohesion.index.

The presented algebras of the large set quotients
-------------------------------------------------

TypeTopology's Quotient.Large constructs set quotients from function
extensionality, propositional extensionality and propositional
truncations, without resizing: the quotient of a type X in 𝓤 by an
equivalence relation with values in 𝓥 is the image of the map that sends
a point to its equivalence class, a subset of X with values in Ω 𝓥, so
it lives in 𝓤 ⊔ 𝓥 ⁺. Its large-set-quotients are an instance of
general-set-quotients-exist at the successor (_⁺) of universes.

The construction of gist.Orbifolds.PresentedAlgebrasFromQuotients,
applied to them, is large-presented-algebras : the actual algebras
presented by generators and relations, with carriers the quotients of
Poly n, which lie in 𝓤₀ ⁺, that is, 𝓤₁. Their universal property
eliminates into algebras of every universe, as the interface requires.

Propositional extensionality for all universes, Prop-Ext, is an explicit
ordinary parameter of this module, in the form in which Quotient.Large
takes it [3, Section 1]. No other assumption supplies it: in particular
it is not derived from the univalence of a single universe. No small
quotient, resizing, effectivity, choice, univalence or crisp datum is
assumed, and the module adds no option and no postulate.

The instance is a module application. Every proof was checked against
the abstract interface of general set quotients, so none is checked
against the internals of Quotient.Large [1, Section 2.4].

[1] Claude Fable 5.2. Plan: formalizing the comparison of Weil algebras
    with presentations, 13 November 2026, Sections 2 and 4.2, with its
    statement companion, Section WG2 (plan SHA-256 b1662ecc…; companion
    SHA-256 47974af8…).
[2] GPT-6 Astra. Review of Fable's Weil plan, 13 November 2026
    (FABLE-WEIL-PLAN-REVIEW-01).
[3] Claude Fable 5.2. Addendum 01 to the plan, 13 November 2026
    (SHA-256 abf31923…).
[4] GPT-6 Astra. Release of gate WG2, 13 November 2026
    (SHA-256 998a4fb0…).

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons using (Prop-Ext)
open import gist.Orbifolds.SmoothLine using (Commutative-Ring)

module gist.Orbifolds.PresentedAlgebrasFromLargeQuotients
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
        (pe : Prop-Ext)
        (𝓡 : Commutative-Ring)
       where

open import Quotient.Large pt fe pe using (large-set-quotients)
open import gist.Orbifolds.PresentedAlgebras fe pt 𝓡 using (Presented-Algebras)
open import gist.Orbifolds.PresentedAlgebrasFromQuotients fe pt 𝓡
 using (presented-algebras-from-quotients)

large-presented-algebras : Presented-Algebras 𝓤₁
large-presented-algebras = presented-algebras-from-quotients large-set-quotients

\end{code}
