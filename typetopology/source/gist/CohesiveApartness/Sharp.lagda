Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 11 November 2026. See the AI disclosure in
gist.CohesiveApartness.index.

The sharp modality ♯, natively.

Agda 2.9.0 adds the modality @♯ to --cohesion, as the right adjoint of
@♭, and allows it on the fields of records [1]. The type ♯ A is then
a record with one field of modality ♯, as in the Agda documentation
[1]. It obeys Shulman's rules for ♯ [2, §3]:

 * in the type ♯ A, every variable occurring in A counts as crisp;

 * an element of ♯ A is defined by copattern matching, after which
   every variable in the context counts as crisp;

 * the field can be projected from a crisp element of ♯ A.

From these rules we derive the unit of ♯, recursion into types of
the form ♯ B, crisp induction (to construct an element of ♯ (C x) for
an arbitrary x of a crisp type, it suffices to construct C x for
crisp x), and elimination on crisp elements. Everything here is
--safe.

Agda 2.8 has no ♯, and so gist.CohesiveApartness.FlatSplit proves the
consequence of crisp induction that this folder needs, that 𝟚 is
♭-discrete, with --flat-split instead.
gist.CohesiveApartness.CrispInduction derives it from the ♯ of this
module, in --safe mode.

The field is called ε♯ rather than ε, so that opening this module
does not take the name ε, which TypeTopology uses for other
purposes.

[1] The Agda documentation, Language, Flat Modality, for Agda 2.9.0.
    https://agda.readthedocs.io/en/latest/language/flat.html

[2] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3
    Numbering as in version 3 of the arXiv preprint.

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

module gist.CohesiveApartness.Sharp where

open import MLTT.Spartan

record ♯ {𝓤 : Universe} (@♯ A : 𝓤 ̇ ) : 𝓤 ̇ where
 constructor sharp
 field
  @♯ ε♯ : A

open ♯ public

\end{code}

The unit, elimination on crisp elements, recursion, crisp induction
and the action on maps.

\begin{code}

unit-sharp : {𝓤 : Universe} {A : 𝓤 ̇ } → A → ♯ A
unit-sharp a .ε♯ = a

crisp-elim-sharp : {@♭ 𝓤 : Universe} {@♭ A : 𝓤 ̇ } (@♭ w : ♯ A) → A
crisp-elim-sharp w = w .ε♯

rec-sharp : {𝓤 𝓥 : Universe} {A : 𝓤 ̇ } {B : 𝓥 ̇ }
          → (A → ♯ B) → ♯ A → ♯ B
rec-sharp f a .ε♯ = f (a .ε♯) .ε♯

crisp-ind-sharp : {@♭ 𝓤 : Universe} {𝓥 : Universe} {@♭ A : 𝓤 ̇ }
                  (C : A → 𝓥 ̇ )
                → ((@♭ x : A) → C x)
                → (x : A) → ♯ (C x)
crisp-ind-sharp C f x .ε♯ = f x

♯-map : {𝓤 𝓥 : Universe} {A : 𝓤 ̇ } {B : 𝓥 ̇ } → (A → B) → ♯ A → ♯ B
♯-map f a .ε♯ = f (a .ε♯)

\end{code}
