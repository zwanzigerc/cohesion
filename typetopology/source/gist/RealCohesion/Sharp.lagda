Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 October 2026. See the AI disclosure in
gist.RealCohesion.index.

The sharp modality ♯ of spatial type theory [1, §3], as module
parameters.

Agda's --cohesion provides the flat modality ♭ and crisp variables,
but, in the released Agda 2.8, not the sharp modality ♯, its right
adjoint. The library agda-unimath [2] postulates ♯ with a unit, a
crisp elimination principle, a crisp induction principle and a modal
induction principle, following earlier developments by Licata [3] and
Myers [4]. We follow its design, with two differences. We take as
assumptions only the parts that we use, namely ♯, its unit, a
recursion principle (a consequence of agda-unimath's induction
principle) and its crisp induction principle. And we take them as the
fields of a record, which our modules take as a parameter, instead of
postulating them. So the modules stay --safe, and every result shows
its dependence on ♯.

The crisp induction principle says that, to construct an element of
♯ (C x) for an arbitrary x of a crisp type A, it suffices to have an
element of C x for every crisp x. This is the type-theoretic content
of the introduction rule of ♯, which makes every variable in the
context crisp [1, §3]. A main consequence is Shulman's Theorem 3.3
[1]: when the goal is codiscrete, all variables may be assumed crisp.
The module gist.RealCohesion.AxiomTObstruction uses only the unit and
crisp induction.

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3
    Numbering as in version 3 of the arXiv preprint.

[2] The agda-unimath library, modules modal-type-theory.sharp-modality
    and modal-type-theory.sharp-codiscrete-types.
    https://unimath.github.io/agda-unimath/
    Comparison revision, not the revision consulted:
    src/modal-type-theory/sharp-modality.lagda.md and
    src/modal-type-theory/sharp-codiscrete-types.lagda.md at commit
    75518656f287c203b41cb7f71df46e02b987a084 of
    https://github.com/UniMath/agda-unimath. The compared declarations
    are the same in the versions from 4264b327 (6 September 2024) to
    that commit, and differ in the earlier ones; see the provenance
    ledger (provenance/EXTERNAL-SOURCES-CURRENT.json).

[3] Dan Licata. cohesion-agda. https://github.com/dlicata335/cohesion-agda

[4] David Jaz Myers. Cohesion. https://github.com/DavidJaz/Cohesion

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

module gist.RealCohesion.Sharp where

open import MLTT.Spartan
open import UF.Retracts
open import UF.Subsingletons

\end{code}

The assumptions. The type ♯ A, its unit, and recursion into types of
the form ♯ B, for all types A and B, and crisp induction for families
over crisp types.

\begin{code}

record Sharp-Modality : 𝓤ω where
 field
  ♯ : {𝓤 : Universe} → 𝓤 ̇ → 𝓤 ̇
  unit-sharp : {𝓤 : Universe} {A : 𝓤 ̇ } → A → ♯ A
  rec-sharp : {𝓤 𝓥 : Universe} {A : 𝓤 ̇ } {B : 𝓥 ̇ }
            → (A → ♯ B) → ♯ A → ♯ B
  crisp-ind-sharp : {@♭ 𝓤 : Universe} {𝓥 : Universe} {@♭ A : 𝓤 ̇ }
                    (C : A → 𝓥 ̇ )
                  → ((@♭ x : A) → C x)
                  → (x : A) → ♯ (C x)

\end{code}

A type is codiscrete if the unit of ♯ has a retraction. Shulman asks
the unit to be an equivalence, which implies this. For propositions,
the only case that we use, the two agree in the presence of the rest
of Shulman's rules, and having a retraction amounts to having a map
♯ P → P.

\begin{code}

module _ (S : Sharp-Modality) where

 open Sharp-Modality S

 is-codiscrete : {𝓤 : Universe} → 𝓤 ̇ → 𝓤 ̇
 is-codiscrete A = has-retraction (unit-sharp {_} {A})

 props-with-a-map-from-sharp-are-codiscrete
  : {𝓤 : Universe} {P : 𝓤 ̇ }
  → is-prop P
  → (♯ P → P)
  → is-codiscrete P
 props-with-a-map-from-sharp-are-codiscrete P-is-prop r =
  r , (λ p → P-is-prop (r (unit-sharp p)) p)

\end{code}

Shulman's Theorem 3.3 [1]: to prove a codiscrete statement about an
arbitrary element of a crisp type, it suffices to prove it for crisp
elements. Packaging the variables of a context into one element of a
Σ-type, this says that, when the goal is codiscrete, all variables
may be assumed crisp. This is agda-unimath's
crisp-ind-sharp-codiscrete.

\begin{code}

 decrispify : {@♭ 𝓤 : Universe} {𝓥 : Universe} {@♭ A : 𝓤 ̇ }
              (C : A → 𝓥 ̇ )
            → ((x : A) → is-codiscrete (C x))
            → ((@♭ x : A) → C x)
            → (x : A) → C x
 decrispify C κ f x = retraction-of unit-sharp (κ x) (crisp-ind-sharp C f x)

\end{code}

Codiscreteness of propositions is invariant under logical equivalence.

\begin{code}

 codiscreteness-of-props-is-invariant-under-↔
  : {𝓤 𝓥 : Universe} {P : 𝓤 ̇ } {Q : 𝓥 ̇ }
  → is-prop Q
  → P ↔ Q
  → is-codiscrete P
  → is-codiscrete Q
 codiscreteness-of-props-is-invariant-under-↔ Q-is-prop (f , g) κ =
  props-with-a-map-from-sharp-are-codiscrete Q-is-prop
   (f ∘ retraction-of unit-sharp κ ∘ rec-sharp (unit-sharp ∘ g))

\end{code}
