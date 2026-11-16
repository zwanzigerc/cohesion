Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 October 2026; the modules for the native ♯ of Agda 2.9.0
added, and three proofs of TightApartness made instances of one lemma,
11 November 2026.

This module is licensed under the GNU General Public License, version 3.
SPDX-License-Identifier: GPL-3.0-only

AI disclosure. The results are joint work of two AI models, GPT-6
Astra and Claude Opus 5.5, who contributed equally to the
mathematics; the solution idea came from GPT-6 Astra, which also
reviewed the formalization. Claude Opus 5.5, an AI model made by
Anthropic, developed the Agda formalization and its exposition at
Colin Zwanziger's prompting from 24 to 27 October 2026. The proof of
Swan-apartness in TightApartness incorporates code copied and modified
from Tom de Jong's implementation in TypeTopology's Apartness.Properties.
The modules Sharp, CrispInduction and Theorems were added on
11 November 2026 by Claude Opus 5.5, prompted by Colin Zwanziger in
another conversation, when the folder moved to Agda 2.9.0; they
follow Shulman's derivation of crisp induction from the sharp
modality. On 11 November 2026, in that conversation, three proofs in
TightApartness became instances of one lemma,
decidable-predicates-spread, with no statement changed. The files
were type-checked with Agda 2.9.0 (release candidate 3) against
TypeTopology commit 52ed2eb of 24 October 2026. Flat, TightApartness
and FlatSplit, which don't need the native ♯, were also checked with
Agda 2.8.0, TightApartness again after that change. TypeTopology's
AI-Policy.md excludes submissions of AI-generated Agda code or prose.
The cohesion repository contains these modules and the accompanying
paper.

 https://github.com/zwanzigerc/cohesion

This folder studies two problems about tight apartness relations in
the presence of the flat modality ♭, formerly listed as open problems
on the nLab page

 https://ncatlab.org/nlab/show/open+problems+in+homotopy+type+theory

See gist.CohesiveApartness.TightApartness for the statements of the
problems, how we read them, the exact scope of the formal results, and
a summary of the results.

 * gist.CohesiveApartness.Flat defines ♭, ♭-discreteness, crisp
   excluded middle, Shulman's Axioms C0 and C1, and the nLab's
   single-generator variant of Axiom C1, which we call singly
   generated punctual cohesion.

 * gist.CohesiveApartness.TightApartness formulates the two problems
   and shows that, over crisp excluded middle, each is equivalent to
   excluded middle. Assuming also propositional extensionality, each
   is then equivalent, under Shulman's Axiom C1, to every generator
   being 0-connected, and under singly generated punctual cohesion to
   the generator being 0-connected. Shulman's Axiom C2 refutes both
   statements (the first over crisp excluded middle). Some of these
   results assume that 𝟚 is ♭-discrete, a theorem of Shulman's type
   theory whose proof needs crisp induction.

 * gist.CohesiveApartness.Sharp defines the sharp modality ♯ natively,
   as a record with a field of modality ♯, which Agda 2.9.0 allows,
   with its unit, recursion, crisp induction and elimination on crisp
   elements.

 * gist.CohesiveApartness.CrispInduction derives from ♯ consequences
   of crisp induction: that 𝟚, which this folder uses, ℕ and ♭ A are
   ♭-discrete, and that the constructor of ♭ respects crisp
   identifications.

 * gist.CohesiveApartness.Theorems restates the main theorems of
   gist.CohesiveApartness.TightApartness without the assumption that
   𝟚 is ♭-discrete.

 * gist.CohesiveApartness.FlatSplit proves that 𝟚 is ♭-discrete
   instead by pattern matching on a crisp element of 𝟚, using Agda's
   flag --flat-split, and restates the same theorems. It is the route
   for Agda 2.8, which has no ♯, and is kept for comparison. Agda
   doesn't allow --flat-split together with --safe and --without-K,
   so this module is not --safe. It is therefore not imported here
   and has to be checked separately.

The problems were posed by the nLab contributor Anonymouse, using the
nLab's definition of axiom C1, so technically they refer to singly
generated punctual cohesion. We take Shulman's paper (arXiv:1509.07584)
as the authority on Axiom C1, and give the main results for both
definitions.

The modules here use Agda's flag --cohesion, which provides the flat
modality and crisp variables. Because --cohesion is infective, every
module that imports them must use it too, and so must this index
file. The library file typetopology.agda-lib sets --no-cohesion, and
gist.index doesn't use --cohesion. This folder is therefore not
imported by gist.index for the moment. How to handle this, if at all,
is a question for the maintainers.

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

module gist.CohesiveApartness.index where

import gist.CohesiveApartness.CrispInduction
import gist.CohesiveApartness.Flat
import gist.CohesiveApartness.Sharp
import gist.CohesiveApartness.Theorems
import gist.CohesiveApartness.TightApartness

\end{code}
