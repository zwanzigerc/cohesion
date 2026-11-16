Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 and 26 October 2026; prose updated 27 October 2026; the
formalizations for nLab problem 4 and for removing Axiom T added
10 November 2026; rational detection and Shulman's Corollary 11.6
added 11 November 2026; moved to Agda 2.9.0 and its native ♯ on
11 November 2026; Shulman's Theorem 11.7 without crisp excluded middle
added 11 November 2026; sequential hitting for functionals added, and
the hitting modules made to share their code, 11 November 2026;
Bolzano–Weierstrass for crisp sequences added 11 November 2026;
duplicated code removed 11 November 2026; the grid, the labels and
Kuhn's lemma in dimensions 0 and 1 added 11 November 2026; the crisp
fixed point on the cube added 12 November 2026; Lemma 4.1, Theorem 4.3
on the cube and Shulman's Theorem 8.32 in apartness form added
12 November 2026; Kuhn's lemma in dimension 2, and with it the square,
added 12 November 2026; strong extensionality, rational detection in n
variables, and the statements of the second addendum added 12 November
2026; Shulman's Theorem 11.5 from Axiom R♭ alone added 12 November
2026; its n-variable form, GPT-6 Astra's Theorem 7.17, added 12 November
2026; the injectivity of the canonical map in n variables added
12 November 2026; the cube form of Shulman's Theorem 12.6 from crisp
excluded middle added 12 November 2026; Theorem 3.3 in n variables, with
every continuous map a value, added 12 November 2026; Shulman's Lemma
8.15 with its scope, a module by Claude Fable 5.2, added 12 November
2026; the multiplication of real numbers, with its laws, added
12 November 2026; Corollary 3.7 for the Euclidean ball, with Shulman's
Theorem 12.4 and Corollary 12.5 for the disc, added 12 November 2026;
Theorem 4.3 for the ball added 12 November 2026; square roots, the
inverse of positive reals and Shulman's Lemma 12.3 in every dimension
added 12 November 2026; Shulman's Lemma 12.3 from crisp excluded middle
and Axiom C1, with modules by Claude Fable 5.2, added 12 November
2026; Shulman's Theorem 12.6 for the square added 12 November 2026;
the exact intermediate value theorem for crisp functions from crisp
excluded middle for 𝓤₀, with a module by Claude Fable 5.2, added
12 November 2026; Shulman's Theorem 12.6 for the disc added 12 November
2026; its form for every real ε > 0 added 12 November 2026; Kuhn's
lemma in every dimension, with the theorems that depended on it,
added 12 November 2026 (13 November UTC); the general crisp
representatives of finite powers added, the prose corrected and the
code reformatted to lines of at most 80 characters, 13 November 2026,
after the final audits; the consolidation (one statement of Kuhn's
lemma, shared lemmas about ♯, and Lemma 12.3 with a retraction of the
inclusion), 13 November 2026; its second part (a common layer for the
arguments from Axiom C1, and the theorems from Axiom C1 and a strictly
rising generator path in place of Axiom R♭), 13 November 2026.

AI disclosure. Except as stated in the next paragraph, the Agda code,
the prose and the mathematical arguments in this folder are by Claude
Opus 5.5, an AI model made by Anthropic, prompted by Colin Zwanziger
in a conversation from 24 to 26 October 2026. The pointers to the Lean
formalization [6] were added on 27 October 2026, in another
conversation with Colin Zwanziger. Arguments due to GPT-6 Astra are
credited where they are used; in particular, the countermodel to the
continuity conjecture and the two principles of
gist.RealCohesion.FiniteHeightContinuity are from the notes [3, 4, 5],
the dyadic witness for nLab problem 1 is Astra's, and the proof that ℕ
is ♭-discrete in gist.RealCohesion.FlatSplit is ported from
agda-unimath (its map ℕ → ♭ ℕ and the proof that this map is a section
of the counit are reused in gist.CohesiveApartness.CrispInduction; the
revision of agda-unimath that the port follows is not recorded), and
the definition of the square root in gist.RealCohesion.RealSquareRoot
is transcribed from it [15].

The formalization of the approximate intermediate value theorem from
Axiom R♭ alone was added on 10 November 2026 by Claude Opus 5.5,
prompted by Colin Zwanziger in another conversation. It consists of
the modules FiniteChainLevels, FiniteChainQuotient,
FiniteChainDiscreteness, FiniteChainLemma, RealLattice, RealLimits,
SequentialHitting, SoftBisection, ApproximateIVTReduction,
ApproximateIVTStatement and ApproximateIVT, and the last section of
FlatSplit. The proof is by Claude Fable 5.2 [7], an AI model made by
Anthropic. The gated reformulation, the alternating graph and
sequential hitting are by GPT-6 Astra [9], who also audited the proof,
including the step from sequential hitting to the theorem. The
formalization follows Fable's blueprint and handoff [8].
FiniteChainLevels and ApproximateIVTStatement are Fable's starter
modules, with their prose adapted to this folder. The rest is by
Claude Opus 5.5, including the real-number layer, which the blueprint
specified but did not prove, and some changes to the blueprint's
indices and constants, which are explained where they occur.

The formalization of results of Shulman's §11 without Axiom T was
added the same day, in the same conversation. It consists of the
modules RationalEnumeration, IntervalHitting, CrispContinuity and
CrispExactIVT, and two sections of FlatSplit. It follows Part A of
Fable's note [10], which GPT-6 Astra audited. The Agda code and the
prose are by Claude Opus 5.5, who replaced the note's use of Lemma S
by interval hitting, a consequence of sequential hitting, and derived
Shulman's Theorem 11.2 from the connectedness of rational intervals
rather than from a new bisection.

The formalization of GPT-6 Astra's rational detection [9, §§2–3] and
its consequences was added on 11 November 2026, in the same
conversation. It consists of the modules Quantizers, PairHitting,
RationalDetection and CrispFunctionsEverywhere, and a section of
FlatSplit. The mathematics is Astra's. The Agda code and the prose
are by Claude Opus 5.5, who built Astra's quantizers as finite sums of
clamps instead of gluing them on an open cover, and reduced
sequential hitting on ℝ² to sequential hitting on ℝ along the path
built in its proof.

The formalization of Shulman's Corollary 11.6 without Axiom T was
added on 11 November 2026, in the same conversation. It consists of
the modules RealBalls, CrispUniformContinuity, CrispExtension and
FlatRealFunctions, and a section of FlatSplit. It follows Part A.4 of
Fable's note [10], which GPT-6 Astra audited. The Agda code and the
prose are by Claude Opus 5.5, who changed the route in two places:
injectivity comes from Astra's rational detection instead of the
concreteness of ℝ, so that it needs neither the sharp modality nor
crisp excluded middle; and the uniform continuity of continuous maps
on bounded intervals comes from the connectedness of crisp rational
intervals instead of a compactness argument.

The move to Agda 2.9.0 was made on 11 November 2026, in the same
conversation, also by Claude Opus 5.5. Agda 2.9.0 provides the sharp
modality ♯ natively. The modules NativeSharp and Theorems, and the
modules Sharp, CrispInduction and Theorems of gist.CohesiveApartness,
were added then. They derive the consequences of crisp induction from
♯, following Shulman's derivation of crisp induction [2, §5], instead
of proving them with --flat-split, and restate the main theorems in
--safe mode. No existing statement changed.

The formalization of Shulman's Theorem 11.7 without crisp excluded
middle, Theorem 7.10 of the revised write-up [11], was added on
11 November 2026, in the same conversation. It consists of the modules
BrouwerStatements, PlateauPath and AnalyticLLPO, and a section of
Theorems. The proof is by Claude Fable 5.2 [11, 12], and GPT-6 Astra
audited it on paper on 11 November 2026, relative to the finite-chain
lemma [12]; it is gate G7 of Fable's blueprint addendum [12].
BrouwerStatements is Fable's starter module for the addendum,
unchanged. The Agda code and the rest of the prose are by Claude Opus
5.5. PlateauPath states the plateau path of SequentialHitting for an
arbitrary sequence, as the addendum asks; SequentialHitting uses it
since gate G8.

The formalization of sequential hitting for functionals, Theorem 7.4
of the revised write-up [11] and the remark after it, was added on
11 November 2026, in the same conversation; it is gate G8 of Fable's
blueprint addendum [12]. It consists of the modules Plateaus and
FunctionalHitting and a section of Theorems. Theorem 7.4 is GPT-6
Astra's sequential hitting, formalized for ℝ in SequentialHitting; its
form for functionals is a remark of Claude Fable 5.2 that has not been
audited on paper [11, 12]. The Agda code and the prose are by Claude
Opus 5.5, who proved the form for functionals by the reduction to one
variable that PairHitting used for pairs, instead of rerunning the
construction pointwise as the addendum suggests. At the same time the
hitting modules were made to share their code, with no statement
changed: Plateaus holds the heights, parity and plateaus that were in
SequentialHitting; SequentialHitting takes its path from PlateauPath
instead of from its own copy; PairHitting is now the instance X = 𝟚 of
FunctionalHitting; and the lemmas within-zero and ψ-at-zero moved from
PairHitting to RealLimits and PlateauPath.

The formalization of Lemma 3.6 of the revised write-up [11], the
Bolzano–Weierstrass lemma for crisp sequences of rational points of the
cube, was added on 11 November 2026, in the same conversation; it is
gate G9 of Fable's blueprint addendum [12]. It consists of the module
CrispBolzanoWeierstrass and additions to CrispRationals. The proof is
Claude Fable 5.2's, in the write-up, by repeated subdivision into 2ⁿ
subcubes; GPT-6 Astra audited it on paper on 11 November 2026 [12]. The
Agda code and the prose are by Claude Opus 5.5. The addendum proposed an
induction on the crisp dimension, which needs crisp induction on ℕ; the
subdivision needs none, because every decision concerns a box, which has
crisp representatives. At the same time, with no statement changed:
CrispRationals gained crisp elimination, and decide-at-rationals and
decide-at-naturals of CrispContinuity are now instances of its
decide-at; CrispConnectedness takes the halves of its intervals from
RationalArithmetic, which now holds the halving shared with
CrispBolzanoWeierstrass, and one bound from NestedIntervals; and
RealOrder, RealLimits and SequentialHitting each gained a lemma used by
CrispBolzanoWeierstrass.

Duplicated code was removed on 11 November 2026, in the same
conversation, after an audit of all modules; Colin Zwanziger asked for
the library to be lean. Each lemma that was proved more than once now
has one proof, in a module that the others import, and lemmas that
TypeTopology already has are defined by TypeTopology's. Old names are
kept as re-exports or one-line definitions, and no statement changed,
except that two special cases in CrispExactIVT gave way to the general
lemmas and three unused helpers were removed. In a second pass,
families of lemmas proved again for each instance became instances of
one lemma or module: halving sequences, for ρ, the thresholds and
levels of DyadicProfile and DyadicLevels, and the lengths in
CrispConnectedness; crisp elimination in two variables and crisp
witnesses, for thirteen places that eliminated over crisp
representatives by hand; following a branch (Cylinders), shared with
BinaryBarObstruction; monotonicity from single steps; one construction
for the two levels of FiniteChainLemma; one induction step in
DyadicLevels; one argument for each pair of mirror cases in
CrispConnectedness; and TypeTopology's map out of the initial frame in
PointlessEnd and its Boolean value of a decision in CrispDecisions.

The grid and the labels of the proof of Corollary 3.7 of the revised
write-up [11], and Kuhn's cubical lemma in dimensions 0 and 1, were
added on 11 November 2026, in the same conversation; they are gate G10
of Fable's blueprint addendum [12]. They consist of the modules
KuhnLemma and CubeGrid and a section of Theorems. The statement of
Kuhn's lemma is Fable's, from BrouwerStatements, after Isabelle's
kuhn_lemma; the labels and their properties are the write-up's. The
Agda code and the prose are by Claude Opus 5.5. The addendum decides
the comparison at a grid point by crisp elimination over the level
and the index vector; CubeGrid also decides the coordinate through its
number, because Fin n is not known to have crisp representatives
without crisp induction. At the same time, with no statement changed,
RationalArithmetic gained the rational two, which CrispBolzanoWeierstrass
and DyadicOscillation defined separately; RealOrder gained
embedding-preserves-≤, and ℝ<-gives-≤ from AnalyticMarkovObstruction;
and Quantizers gained mult-half, of which mult-double is now an
instance.

The crisp fixed point on the cube, Corollary 3.7 of the revised
write-up [11] for the cube in place of the Euclidean ball, was added
on 12 November 2026, in the same conversation; it is gate G11 of
Fable's blueprint addendum [12]. It consists of the modules
RationalGrid and CubeFixedPoint and a section of Theorems. The
statements are Fable's targets Target-3-7-crisp and Target-3-7-sharp
from BrouwerStatements; the proof is the write-up's, in the form of
the addendum: first for a crisp map from ℝⁿ to the cube, then for a
crisp self-map of the cube through clamping. The Agda code and the
prose are by Claude Opus 5.5. At the same time, with no statement
changed: the rational part of CubeGrid moved to the new module
RationalGrid, which has no parameters and which CubeGrid re-exports,
and mult with its first facts moved from Quantizers, which re-exports
them, to RationalArithmetic, because Agda compared real numbers at
grid points slowly while grid points depended on a module parameter.
RealLattice gained difference-of-≤ and ≤-from-difference, and
RationalGrid gained mesh-antitone and grid-point-bounds, the rational
half of grid-points-are-in-cube.

Lemma 4.1 of the revised write-up [11], Theorem 4.3 for the cube in
place of the Euclidean ball, and Shulman's Theorem 8.32 without Axiom
C1 in its apartness form were added on 12 November 2026, in the same
conversation; they are gate G12 of Fable's blueprint addendum [12].
They consist of the modules PositiveTerms and ApproximateCubeFixedPoint,
additions to AnalyticMarkovObstruction and AxiomTObstruction, and
sections of Theorems. The statements are Fable's targets Target-4-1,
Target-4-3 and Target-8-32 from BrouwerStatements; the proofs are the
write-up's, in the form of the addendum. The Agda code and the prose
are by Claude Opus 5.5. Lemma 4.1 clamps the terms to shrinking
intervals instead of halving them, so that no multiplication of real
numbers is needed. At the same time, with no statement changed:
RealLattice gained lemmas on the positivity of sums, differences,
maxima and minima; CubeFixedPoint exports the converging grid points
of the crisp fixed point and the agreement of the clamped extension
with the map on the cube; and the extension of a function on Fin m by
a first value moved from CrispBolzanoWeierstrass, which keeps its
names as instances, to CrispRationals, for any type of values.

Kuhn's cubical lemma in dimension 2, and with it Corollary 3.7 and
Theorem 4.3 of the revised write-up [11] for the square with no
combinatorial hypothesis, were added on 12 November 2026, in the same
conversation; they are gate G13 of Fable's blueprint addendum [12].
They consist of additions to KuhnLemma and to the last section of
Theorems. The proof of Kuhn's lemma is Fable's parity argument from
the addendum: tags on the grid, doors between tags τ₀ and τ₁, and
exclusive-or sums over the triangles of the grid. The Agda code and
the prose are by Claude Opus 5.5. agda-unimath has no Kuhn or Sperner
lemma, and the sums are short, so nothing was transcribed.

Strong extensionality and rational detection in n variables, and the
statements of results above in the words of Claude Fable 5.2's second
addendum [14], were added on 12 November 2026, in the same
conversation; this is gate G16 of the second addendum. They consist of
the modules ShulmanWeakeningsStatements, StrongExtensionality,
ContinuityForms and FinVectors, an addition to RationalDetection, and a
section of Theorems. ShulmanWeakeningsStatements is Fable's starter
module for the second addendum, unchanged. Strong extensionality is
Lemma 7.12 of the write-up's revision of 12 November [13], observed by
GPT-6 Astra and by Claude Fable 5.2 on 10 November; its proof is the
addendum's, which Astra audited. Rational detection in n variables is
the addendum's induction on n, the first step of the proof of Lemma
7.15 of [13]. The Agda code and the rest of the prose are by Claude
Opus 5.5. ContinuityForms shows that the library's two forms of
continuity at a point, by rational intervals and by rational balls,
agree with the strict ε-δ form of the starter module, so that
Shulman's Theorem 11.5 and Corollary 11.6 are stated in his words. At
the same time, with no statement changed, Fin-cons and
Fin-cons-of-parts moved from CrispRationals, which re-exports them, to
the new module FinVectors, which does not use --cohesion. Nothing was
transcribed from agda-unimath; the second addendum's survey lists
nothing to transcribe for this gate.

Shulman's Theorem 11.5 from Axiom R♭ alone, Theorem 7.14 of the
write-up's revision of 12 November [13], was added on 12 November 2026,
in the same conversation; it is gate G23 of the second addendum [14].
It consists of the modules IndistinguishablePoints and
CrispFunctionsAreContinuous, additions to CrispRationals, and a section
of Theorems. The proof is Shulman's, with strong extensionality in
place of his two uses of Axiom T, as Claude Fable 5.2's note proposes;
GPT-6 Astra audited it on paper on 12 November 2026. Lemma 7.13 of
[13], the construction without ʃ₀ that replaces components by maps to
𝟚, is Fable's. The Agda code and the prose are by Claude Opus 5.5, who
simplified the route in three places: the second set of each cover is
a half-line, so that the four modifications of the function in [13]
are not needed; Lemma 7.13 is stated for subsets of the whole line;
and its quotient is taken of double duals by the relation of [13]
itself, without images or a set-pushout. Nothing was transcribed from
agda-unimath; the second addendum's survey lists nothing to transcribe
for this gate.

The n-variable form of Shulman's Theorem 11.5 from Axiom R♭ alone,
Theorem 7.17 of [13], by GPT-6 Astra, was added on 12 November 2026, in
the same conversation; it is gate G24 of the second addendum [14], and
with it gate G18 (Remark 3.4 of [13], with crisp excluded middle), which
the second addendum calls a corollary. It consists of the modules
DigitCodes, DigitCells, DigitCurve and CrispFunctionsOfSeveralVariables,
additions to RealLattice, RealLimits, RationalDetection and
ContinuityForms, and a section of Theorems. The proof is Astra's:
dyadic detection, a digit-interleaving curve P whose values at the
codes of dyadic points are those points, and the transfer of the
one-variable theorem along P. It was audited independently on Astra's
side, and Claude Fable 5.2 audited it on paper and checked the coding
in exact arithmetic. The Agda code and the prose are by Claude Opus
5.5, who changed three details: the curve has 2n + 1 coordinates and
the centre 1/4, whose orbit is 1/4, 3/4 for every n; the cells are
intervals of radius 2⁻ᵏ/3 around 1/3 and 2/3 rather than dyadic cells,
so that no floor function is needed; and the curve's coordinates are
the series of PositiveTerms, half of Astra's, with the terms that Fable
suggests. At the same time, with no statement changed, the finite
minima moved from ApproximateCubeFixedPoint, which re-exports them, to
RealLattice. Nothing was transcribed from agda-unimath: the survey
points to floors, powers and geometric sequences of rationals, which
the cells and the library's halving sequences make unnecessary.

The injectivity of the canonical map ♭ (ℝⁿ → ℝ) → (♭ ℝⁿ → ♭ ℝ) from
Axiom R♭ alone, the first part of Theorem 3.3 of [13] in n variables,
was added on 12 November 2026, in the same conversation; with the
continuity of the values from gate G24 it is gate G20 of the second
addendum [14]. It consists of the module FlatFunctionsOfSeveralVariables
and a section of Theorems. The route is the addendum's: crisp functions
that agree at crisp points agree at rational points, hence everywhere,
by rational detection in n variables. The Agda code and the prose are
by Claude Opus 5.5. Nothing was transcribed from agda-unimath.

The third part of Theorem 3.3 of [13] in n variables, that every
continuous map ♭ ℝⁿ → ♭ ℝ is a value of the canonical map, from crisp
excluded middle and Axiom R♭, was added on 12 November 2026, in the
same conversation; it is gate G21 of the second addendum [14]. It
consists of the modules CrispBisection, CrispUniformContinuityOnBoxes
and CrispExtensionOnBoxes, a section of FlatFunctionsOfSeveralVariables,
Fin-choice in FinVectors, and a section of Theorems, which also gives
Shulman's Corollary 11.6 in his words with crisp excluded middle for 𝓤₀
only. The extension is the addendum's, with rational boxes in place of
rational intervals. The uniform continuity on boxes takes a route of
Claude Opus 5.5's, not the addendum's: the bisection behind
Bolzano–Weierstrass is applied to the boxes on which the values of the
map spread, in place of a crisp sequence of grid points. This route
was not audited when it was added; GPT-6 Astra's final source audit
of 13 November 2026 (UTC) covers it. For this the bisection became a
module of its own,
CrispBisection, of which CrispBolzanoWeierstrass is now an instance,
with its names and their types unchanged. The Agda code and the prose
are by Claude Opus 5.5. Nothing was transcribed from agda-unimath. On
the same day, at Colin Zwanziger's request, a sentence was added to the
comment on Crisp-Real-Continuity in CrispRealAnalysis, saying where it
is now derived.

The module DiscreteSets, Shulman's Lemma 8.15 with its scope, is by
Claude Fable 5.2 (11 November 2026; gate G15 of the blueprint addendum
[12]); the observation that the printed proof needs a crisp set, and the
example of the type P → 𝟚, are GPT-6 Astra's. It was added to this
folder on 12 November 2026 by Claude Opus 5.5, at Colin Zwanziger's
decision, with its code unchanged and two sentences of its prose
changed, which pointed to a module with --flat-split that is not part
of the folder. Its three results are stated in Theorems, in --safe
mode, by Claude Opus 5.5.

The multiplication of real numbers, with its laws, was added on
12 November 2026, in the conversation of gate G21, as the first step
(E1) of gate G14 of the second addendum [14]: the modules
RationalBoxExtension, RationalProducts and RealMultiplication, and
Fin-pair in FinVectors. The addendum suggests transcribing it from
agda-unimath, where it rests on the arithmetic of closed rational
intervals. Instead, RationalBoxExtension makes the extension of
CrispExtensionOnBoxes generic in its sample points, and
RealMultiplication extends the multiplication of rationals with it;
CrispExtensionOnBoxes is now an instance, with its names and their
types unchanged. Helpers moved from CrispUniformContinuity,
CrispExtension, CrispExactIVT, CrispUniformContinuityOnBoxes and
CrispExtensionOnBoxes to RealBalls, RationalArithmetic, RealOrder and
RationalBoxExtension, and their old modules re-export them with their
types unchanged. The
Agda code and the prose are by Claude Opus 5.5. Nothing was transcribed
from agda-unimath.

Corollary 3.7 of the write-up for the Euclidean ball, and with it
Shulman's Theorem 12.4 and Corollary 12.5 for the disc, was added on
12 November 2026, in the same conversation, as step E2 of gate G14: the
modules RealReciprocal and EuclideanBall, additions to RationalProducts
and RealMultiplication, and a section of Theorems. The retraction
x ↦ x / max(1 , ‖x‖²) of ℝⁿ onto the ball is the square-root-free
retraction of Fable's addendum [14], which Codex audited on
12 November 2026. The Agda code and the prose are by Claude Opus 5.5.
Nothing was transcribed from agda-unimath.

Theorem 4.3 of the write-up for the ball was added on 12 November 2026,
in the same conversation, as step E3 of gate G14: the module
RationalVectors, additions to RationalProducts, RealMultiplication
(negation and products bounded above) and EuclideanBall, and two
results in Theorems. It is transferred from the cube form through the
retraction, which is nonexpansive; the transfer and the proof of
nonexpansiveness are those of Codex's audit of 12 November 2026
(parts D and E). The Agda code and the prose are by Claude Opus 5.5.
Nothing was transcribed from agda-unimath.

Shulman's Lemma 12.3 from crisp excluded middle and Axiom T, without
his Axiom C1 and in every dimension, was added on 12 November 2026, in
the same conversation, as step E4 of gate G14: the modules RealAlgebra,
RealSquareRoot and EuclideanSphere, additions to RationalBoxExtension
(the density principle near a point), RationalProducts,
RealMultiplication, RealReciprocal (the inverse of positive reals) and
EuclideanBall, and a section of Theorems. The removal of C1 and the
extension to every dimension are Remark 3.8 of the write-up [13]; the
retraction onto the sphere and its two equations are those of GPT-6
Astra's audit of 12 November 2026 (part B). The definition of the square
root in RealSquareRoot is transcribed from agda-unimath [15], module
real-numbers.square-roots-nonnegative-real-numbers at commit 7551865,
under its MIT licence, a copy of which is LICENSE-agda-unimath.md in
this folder; its properties have our own proofs. The rest of the Agda
code and the prose are by Claude Opus 5.5.

Shulman's Lemma 12.3 from crisp excluded middle and Axiom C1, without
Axiom T (gate G27 of the second addendum [14], revision 5), was added on
12 November 2026, in the same conversation, after GPT-6 Astra's review
released it. The theorem and its proof are GPT-6 Astra's (12 November
2026), audited by Claude Fable 5.2. The modules BoundaryRetractionFromC1,
BoundaryRetractionFromC1Statements, BoundaryRetractionFromC1Targets and
SphereRetractionFromC1 are by Claude Fable 5.2; the first contains a
reproduction of Astra's module C1FiniteChainBridge. Claude Opus 5.5
added them with their code unchanged except two changes that Astra
asked for: BoundaryRetractionFromC1Targets repeats the equality
bits-agree of Theorems instead of importing Theorems, and
SphereRetractionFromC1 has a new last section that gives its retraction
as a retract in the sense of EuclideanSphere; one sentence of the prose
of BoundaryRetractionFromC1 and the first paragraphs of the other three
headers were changed. The section of Theorems that states the results
is by Claude Opus 5.5.

Shulman's Theorem 12.6 for the square, from univalence and Axiom R♭
(gate G25), was added on 12 November 2026, in the same conversation, by
the proof of revision 2 of Fable's note [16], which GPT-6 Astra audited
on 12 November 2026. The module DiscreteConnectedTypes is Claude Fable
5.2's scratch check of Lemma 1 of the note, added with its code
unchanged; Collapse, CrispQuotients, DoubleCover, SquareEstimates and
ApproximateBrouwerSquare, and the statement in Theorems, are by Claude
Opus 5.5, following the note.

The exact intermediate value theorem for crisp functions without Axiom
T from crisp excluded middle for 𝓤₀, the target Target-3-5, was added on
12 November 2026, in the same conversation, as Fable proposed after
Astra's audit of the targets. The module CrispExactIVTFromTotalOrder is
Claude Fable 5.2's scratch module CrispExactIVTSharpCheck, added with its
code unchanged except the module name, and one sentence of its prose
changed; the three statements in Theorems and their proofs are Fable's
(the scratch module Target35Check), placed there by Claude Opus 5.5.

Shulman's Theorem 12.6 for the round disc (gate G26) was added on
12 November 2026, in the same conversation, by Corollary 4 of Fable's
note [16]: the module ApproximateBrouwerDisc and its statement in
Theorems are by Claude Opus 5.5; the nonexpansiveness of the retraction
is Lemma 5 of the note, from part D of Codex's audit.

Kuhn's lemma in every dimension, the last item of gate G14, was added
on 12 November 2026 (13 November UTC), in the same conversation, by
the route of Claude Fable 5.2's note [17], revision 3, which GPT-6
Astra audited: the modules KuhnCounting and KuhnLemmaGeneral, and the
forms of the theorems in Theorems without Kuhn's lemma as a
hypothesis, are by Claude Opus 5.5. The route is John Harrison's
proof, in Isabelle/HOL's Brouwer_Fixpoint.thy, translated from HOL
Light by Robert Himmelmann, with LCP [18]; no Isabelle text is
translated, and the BSD three-clause notice of that file is
ISABELLE-COPYRIGHT in this folder.

The final repairs were made on 13 November 2026 by Claude Opus 5.5,
prompted by Colin Zwanziger in another conversation, after the final
audits by Claude Fable 5.2 [19] and GPT-6 Astra, following Fable's
repair plan [19, Section 9] as reviewed by Astra. The module
CrispFinitePowers, the general form of the crisp representatives of
functions on Fin n that gate G9 of the blueprint addendum [12] asks
for, adapts Fable's scratch check FinitePowersCheck. The prose of
several modules was corrected where it had become stale: the routes
to crisp induction, the status of targets now proved or not
commissioned, the scope of a continuity theorem, a credit and an
inequality. The code was reformatted to lines of at most 80
characters, except eight lines of gist.RealCohesion.Theorems that each
consist of one of four names longer than that, which are kept. Apart
from the new module and its import here, the code changed in
whitespace only, and no statement changed.

The consolidation was made on 13 November 2026 by Claude Opus 5.5,
prompted by Colin Zwanziger in the same conversation as the final
repairs, following steps K1, K2, K3 and K6 of Claude Fable 5.2's
consolidation plan [20], as released by GPT-6 Astra. The statement of
Kuhn's lemma, which KuhnLemma and BrouwerStatements defined
separately, moved unchanged to the new module KuhnStatement; both
modules name it by typed aliases, so that bits-agree holds by refl and
the transports along it were removed. The two lemmas about ♯ that
BoundaryRetractionFromC1, BoundaryRetractionFromC1Targets and
gist.Orbifolds.CrispTruncation proved separately moved to the new
module
gist.CohesiveApartness.SharpProperties, which those modules name by
typed aliases. Shulman's Lemma 12.3 for the ball is also stated with
a retraction of the inclusion of the sphere as its conclusion, with
the hypotheses of the existing forms, in EuclideanSphere,
SphereRetractionFromC1 and Theorems. No existing name was removed,
and no existing statement changed.

The second part of the consolidation was made on the same day by Claude
Opus 5.5, in the same conversation, following steps K4 and K5 and W1 to
W4 of the same plan [20], as corrected by its addendum 01 [21] and
released by GPT-6 Astra [22]. Three new modules form a common layer:
gist.RealCohesion.BooleanTests (a map into a type with decidable
equality is constant when every map into 𝟚 is), without parameters;
gist.RealCohesion.PunctualCohesion, the consequences of Axiom C1 for an
ordinary family of generators, without reals; and
gist.RealCohesion.Constancy, the constancy of maps from ℝ to the
quotient Q of levels by finite chains, the strictly rising generator
path NC, and the transfer lemma for sets, without modalities. What
FiniteChainDiscreteness, CrispDiscreteness, BoundaryRetractionFromC1,
DiscreteSets, RealSubsetShape, ApproximateBrouwerSquare,
gist.Orbifolds.C1Discreteness, gist.Orbifolds.Nullification and
gist.Orbifolds.EtaleSourceMaps proved separately is now an instance of
these, under the old names and types. The theorems of
gist.RealCohesion.Theorems that use Axiom R♭ only through the constancy
of maps from ℝ to Q (46, W2), those that pass it to a lower module (24,
W3) and the three from univalence and Axiom R♭ for the square and the
disc (W4) have forms from Axiom C1 for an ordinary family of generators
and a strictly rising generator path in ℝ, merely, stated in the new
module gist.RealCohesion.TheoremsFromC1: for W3 the lower modules
IndistinguishablePoints, CrispFunctionsAreContinuous,
CrispFunctionsOfSeveralVariables, FlatRealFunctions,
FlatFunctionsOfSeveralVariables and DiscreteSets have general modules,
and for W4 the new plain module gist.RealCohesion.HigherTransfer, which
is outside the Agda 2.8 comparison closure, transfers nullness to ℝ for
types that need not be sets. Each theorem under Axiom R♭ keeps its name
and type and is the instance of its form for the one generator ℝ, whose
identity map rises from 0 to 1. The theorems that use the converse half
of Axiom R♭ for a type about which nothing else is known keep Axiom R♭.
gist.RealCohesion.FlatSplit also states the constancy from Axiom C1 and
a merely rising generator path, and the approximate intermediate value
theorem with a rational witness from it, so that the weakening is
checked with Agda 2.8 too. No existing name was removed, and no
existing statement changed.

All files were type-checked with Agda 2.9.0 (release candidate 3)
against TypeTopology commit 52ed2eb of 24 October 2026. The files
that existed before the move to Agda 2.9.0 were also checked with Agda
2.8.0, in the versions of that time, in the snapshot before the move.
After the final repairs, and again after the consolidation,
gist.RealCohesion.FlatSplit, with all the modules that it imports, none
of which uses the native ♯, was checked with the released Agda 2.8.0;
the other files use Agda 2.9.0. The modules are maintained in
https://github.com/zwanzigerc/cohesion. TypeTopology's AI policy
governs submissions to its own repository.

Acknowledgement. We thank GPT-6 Astra for several of the arguments,
for suggesting which properties of the countermodels to formalize, for
the plans of the formalizations of the finite-height obstruction and
of nLab problem 1, and for the semantic audit of the counterexample to
nLab problem 1. We thank Codex for the plans of the
conditional refutations of the analytic Markov principle, the full fan
theorem and Axiom T. We thank Claude Fable 5.2 for the proof of the
approximate intermediate value theorem from Axiom R♭ alone and for the
plan of its formalization, and GPT-6 Astra for the ingredients of that
proof named above and for its audits. We thank Fable for the note on
removing Axiom T, and Astra for its audit and for rational
detection. We thank Fable for the proof of Theorem 7.10 of the
write-up, for the form of sequential hitting for functionals, for the
proof of Lemma 3.6 and for the blueprint addendum, and Astra for the
audits of Theorem 7.10 and Lemma 3.6.

This folder formalizes parts of the research notes [1]. They answer
four of the problems listed under "Real-cohesive homotopy type
theory" on the nLab page

 https://ncatlab.org/nlab/show/open+problems+in+homotopy+type+theory

and study questions left open in Shulman's paper [2]. Several answers
in [1] are about models, for instance independence results, while
Agda's --cohesion reasons inside the theory. For those we formalize
some of the frame-level properties of the models that the arguments
use, relative to hypotheses on the frames involved. Assuming such
properties as hypotheses inside the theory only gives conditional
results, not independence. We formalize such conditional results too:
internal refutations of the principles in question from hypotheses
abstracted from the countermodels.

The nLab problems treated here. The ordinary sheaf countermodel for
questions 2 and 3 was verified in unpublished Lean.

 1. Assuming Axiom R♭, is the shape of every subset of ℝ a set? No:
    it fails in Shulman's intended model [1, Theorem 5.3], by a
    counterexample of Claude Opus whose semantic audit by GPT-6 Astra
    was positive. It holds for codiscrete subsets, assuming crisp
    excluded middle and Axioms R♭ and T [1, Theorem 5.5]. The model
    statements are not formalized.
    Conditional internal refutation, formalized, following a gameplan
    by Astra [23]: the shape of the image of a concrete crisp function
    g : ℝ → ℝ, a subtype of TypeTopology's Dedekind reals, is not a
    set, so not every subset of ℝ, and not even every crisp one, has
    a set as its shape (gist.RealCohesion.RealSubsetShape). The
    hypotheses are univalence, propositional truncations, a
    reflection onto the ℝ-null types, that 𝟚 is ♭-discrete, which
    gist.RealCohesion.Theorems removes in --safe mode with the proof
    of gist.CohesiveApartness.CrispInduction, from the native ♯, and
    gist.RealCohesion.FlatSplit with --flat-split, and the following
    principles, which hold in Shulman's intended model (the informal
    arguments are in gist.RealCohesion.RealSubsetShape; they are not
    formalized):
    crisp excluded middle; the continuity of crisp real functions at
    crisp points, a weak form of Shulman's Theorem 11.5 [2], which is
    stated with Axioms R♭ and T and whose proof also uses crisp
    excluded middle; unique Boolean real-path descent; Axiom R♭; and
    that the type of two-element types is modal. Descent and the
    modality of the type of two-element types are additional
    principles, not derived from Shulman's axioms, and Axiom T is not
    assumed. The function g extends a 1-Lipschitz rational function
    whose graph has plateaux and bumps of alternating signs
    accumulating at 0 (gist.RealCohesion.DyadicProfile); all of its
    properties that the argument uses are proved. The continuity
    hypothesis is now a theorem: it follows from crisp excluded middle
    and Axiom R♭, without Axiom T (gist.RealCohesion.CrispContinuity),
    and gist.RealCohesion.FlatSplit restates the three theorems
    without it. Since gate G23 it follows from Axiom R♭ alone
    (R♭-gives-crisp-real-continuity in gist.RealCohesion.Theorems).

 2. Does the analytic Markov principle, which Shulman adopts as
    Axiom T, follow from crisp excluded middle and Axiom R♭? No: it
    is independent of these and Axiom AC [1, Theorem 2.5]. The
    countermodel adds to the Cartesian spaces locales X_e that look
    like a half-open interval whose endpoint is a pointless locale.
    gist.RealCohesion.PointlessEnd formalizes an abstract version of
    their frames, as an Artin gluing, and the frame-level facts used
    in [1, Theorem 2.5(i)]: every point lies in the collar, the collar
    is not 𝟏, and the coordinate sends the positive half-line to the
    collar. These results are relative to hypotheses on the frames
    involved, which hold classically for the frames in [1] but are not
    verified in Agda. gist.RealCohesion.Cylinders and
    gist.RealCohesion.CohenFrame give a constructive pointless end, and
    gist.RealCohesion.PointlessEndExample shows that the hypotheses are
    consistent.
    For crisp real numbers the principle does follow from crisp
    excluded middle (gist.RealCohesion.CrispDiscreteness).
    Conditional internal refutations, formalized. Two kinds of data,
    abstracted from the countermodel, refute the principle
    (gist.RealCohesion.AnalyticMarkovObstruction): a dense positive
    family, that is, a map t : X → ℝ such that ¬¬ (0 < t x) for every
    x, but not (0 < t x for every x), and the five conditions B1–B5
    of a binary bar, which give such a family. With crisp excluded
    middle, the same data refute Axiom T, for an assumed interface to
    the modality ♯ (gist.RealCohesion.AxiomTObstruction). The
    frame-level forms of B1–B4 in the countermodel are formalized
    (gist.RealCohesion.BinaryBarFrame). That the countermodel realizes
    the data internally is argued informally in [1] and is not
    formalized in Agda. The Lean libraries [6] formalize it for the
    1-topos of sheaves of sets on a smaller site, prove Axiom R♭,
    crisp excluded middle and sharp choice there, and refute there
    the analytic Markov principle, Axiom T and the full fan theorem.

 3. Does the full fan theorem follow? No, by the same model
    [1, Theorem 2.5]. The frame-level failure, a bar that no cover
    bars uniformly, is in gist.RealCohesion.PointlessEnd, relative to
    the same hypotheses. Conditional internal refutation, formalized:
    a family of splitting bars that don't all contain the empty word
    refutes the full fan theorem
    (gist.RealCohesion.BinaryBarObstruction), and the five conditions
    B1–B5 give such a family
    (gist.RealCohesion.AnalyticMarkovObstruction).

 4. Can crispness be removed from Shulman's approximate intermediate
    value theorem? Yes, assuming only Axiom R♭ [1, Theorems 4.2 and
    7.8]. The proof is by Claude Fable 5.2, with ingredients from
    GPT-6 Astra, and Astra audited it [7, 9]. An earlier answer
    assumed crisp excluded middle and Axioms R♭ and T.
    Formalized, for TypeTopology's Dedekind reals
    (gist.RealCohesion.ApproximateIVT): for f : ℝ → ℝ and
    p q a b : ℝ, none of them crisp, with p < q, f a < q and
    p < f b, there merely is x with p < f x < q. The hypotheses are
    Axiom R♭, as an ordinary hypothesis rather than a crisp one, and
    the ♭-discreteness of 𝟚. The module parameters are function
    extensionality, propositional extensionality, propositional
    truncations and crisp-ap-^♭. gist.RealCohesion.FlatSplit proves
    crisp-ap-^♭ and the ♭-discreteness of 𝟚 by crisp induction, which
    leaves Axiom R♭ as the only hypothesis. No excluded middle, Markov
    principle, Axiom T, choice, univalence or set-quotient axiom is
    assumed. The proof goes through a quotient Q of binary sequences
    by finite chains. Under Axiom R♭, Q is ♭-discrete, so every map
    ℝ → Q is constant (gist.RealCohesion.FiniteChainDiscreteness).
    The rest of the proof uses only this constancy and is --safe
    without --cohesion. It consists of the finite-chain lemma,
    Astra's sequential hitting, and a soft bisection
    (gist.RealCohesion.FiniteChainLemma, SequentialHitting and
    SoftBisection). Also formalized: Shulman's crisp theorem by a
    different route (gist.RealCohesion.CrispDiscreteness), and the
    reduction of the non-crisp theorem to the ℝ-nullness of certain
    sets (gist.RealCohesion.OvertConnectedness). With rational
    detection, the witness can be taken rational [1, Theorem 4.2]
    (gist.RealCohesion.RationalDetection; FlatSplit states it from
    Axiom R♭ alone).

The two questions about tight apartness are treated in gist.CohesiveApartness.

Follow-up questions [1, §6]:

 * Crispness under Shulman's axioms. Do the approximate intermediate
   value and Brouwer fixed-point theorems hold for non-crisp functions
   assuming only Axiom R♭ (and univalence)? For the intermediate value
   theorem, yes, and this is formalized; see nLab problem 4. For the
   Brouwer fixed-point theorem we give a counterexample in separate work. For a pointed type,
   overt connectedness is equivalent to the nullness of all the sets
   𝟚-mod P, obtained from 𝟚 by identifying ₀ and ₁ when P holds, and
   ℝ-nullness of all of them gives the non-crisp intermediate value
   theorem (gist.RealCohesion.OvertConnectedness). The proof from
   Axiom R♭ does not go through these sets. For crisp P, axiom
   C1 makes 𝟚-mod P ♭-discrete, which under Axiom R♭ gives Shulman's
   Theorems 11.3 and 11.4 (gist.RealCohesion.CrispDiscreteness).

 * Shulman's continuity conjecture: do Axioms R♭ and AC imply that
   ʃ (A^S) → (ʃ A)^S is an equivalence?
   - Countermodel, not formalized in Agda. The research notes
     [3, 4, 5] give, at an informal level of rigour, a countermodel
     constructed with GPT-6 Astra. It is a pre-cohesive Grothendieck
     topos over sets, on a site of topological spaces built from the
     long ray whose covers include certain open surjections, and its
     ∞-topos of sheaves. The Lean libraries [6] formalize the
     Grothendieck topos: its comparison Π (A^ℕ) → (Π A)^ℕ is not
     injective, Axiom R♭, crisp excluded middle and sharp choice hold
     in it, and so do set-level readings of the two principles
     described next. Verified in unpublished Lean. The higher result has a paper proof.
   - Conditional internal refutation, formalized. The notes isolate
     two principles that hold in the countermodel: the finite-height
     principle and a tower of unbounded depth. From these and
     countable choice for crisp families we derive that the comparison
     ʃ (A^ℕ) → (ʃ A)^ℕ is not an equivalence for a crisp set A
     (gist.RealCohesion.FiniteHeightContinuity). The real-cohesive
     instance, with real paths, is gist.RealCohesion.RealShapeContinuity;
     the version with the discrete axiom of choice is in
     gist.RealCohesion.FlatSplit. The two principles are additional
     hypotheses, not consequences of Shulman's axioms. The
     finite-height principle holds in Shulman's intended model; it is
     the tower that is absent there.
   - Positive results. The conjecture holds in every ∞-sheaf model of
     Axiom R♭ on a suitable site of locales whose covers are the open
     covers [1, Proposition 6.1 and Remark 6.2], which is not
     formalized. The countermodel escapes this through its non-open
     covers. Formalized: axiom C1 and the discrete axiom of choice,
     which follow from Axioms R♭ and AC [2, Theorem 6.30], give crisp
     excluded middle, by a Diaconescu argument
     (gist.RealCohesion.CrispDiscreteness). And, for any modality, a
     product of types that come with contractions along a connected
     type is connected, a special case observed by GPT-6 Astra
     (gist.RealCohesion.ShapeProducts). Supplied contractions are much
     stronger than the mere agreement of zero-shapes in the tower.

 * Shulman's stronger choice formula (3.2) holds in every ordinary local
   topos whose base satisfies choice [1, §6]. In the (2,1)-category of
   groupoid-valued stacks, (3.2) fails at Bℝ while sharp choice (3.3)
   holds for every 0-truncated index map. Verified in unpublished Lean.

The two further questions that Shulman raises in passing, on the
functions ℝⁿ → ℝ and on removing crispness from the approximate
Brouwer fixed-point theorem, are answered in [1, Theorems 3.3 and
4.3], and both answers are formalized, for every crisp dimension n
(see below and gist.RealCohesion.Theorems). The first assumes crisp
excluded middle and Axiom R♭; two of its three parts need Axiom R♭
alone. The second is formalized for the cube and for the ball from
crisp excluded middle and Axioms R♭ and T, without univalence. The
case n = 1 of the first is Shulman's Corollary 11.6, which is
formalized without Axiom T (see the next paragraph).

Axiom T in Shulman's §§11 and 12. Shulman tags Theorems 11.2 and 11.5,
Corollary 11.6, Lemma 12.3, Theorem 12.4 and Corollary 12.5 with Axiom
T. Fable's note [10], audited by GPT-6 Astra, removes it from all of
them, keeping crisp excluded middle; the note's replacement for Lemma
12.3 treats crisp functions only (see also [1, §3]). The T-free Lemma
12.3 of this library, from crisp excluded middle and Axiom C1 (gate
G27; gist.RealCohesion.SphereRetractionFromC1 and
gist.RealCohesion.BoundaryRetractionFromC1), treats arbitrary
fixed-point-free maps, in every positive dimension. Formalized, from
crisp excluded middle and Axiom R♭: the continuity of crisp functions at
crisp points, which is Theorem 11.5 at crisp points, and sequential
continuity (gist.RealCohesion.CrispContinuity); and Theorem 11.2 for
crisp witnesses (gist.RealCohesion.CrispExactIVT). With GPT-6 Astra's
rational detection, which follows from Axiom R♭ alone
(gist.RealCohesion.RationalDetection), both extend to arbitrary
points: Theorem 11.5, continuity at all points of a neighbourhood,
and Theorem 11.2 for arbitrary witnesses
(gist.RealCohesion.CrispFunctionsEverywhere). Fable's note instead
uses Shulman's Corollary 8.16, which needs ♭ to commute with
propositional truncation, and which is unavailable for TypeTopology's
truncations. Also formalized is Corollary 11.6: the canonical map
♭ (ℝ → ℝ) → (♭ ℝ → ♭ ℝ) is an embedding whose image consists of the
ε-δ continuous maps (gist.RealCohesion.FlatRealFunctions); that it is
an embedding needs Axiom R♭ alone. gist.RealCohesion.Theorems states
these results assuming only crisp excluded middle and Axiom R♭, in
--safe mode, and so does gist.RealCohesion.FlatSplit, with
--flat-split. gist.RealCohesion.Theorems also states Theorem 11.5 and
Corollary 11.6 in Shulman's words, as in the starter module of the
second addendum [14] (gist.RealCohesion.ShulmanWeakeningsStatements):
continuity by rational intervals and by rational balls is converted to
his strict ε-δ form (gist.RealCohesion.ContinuityForms). Theorem 11.5
holds from Axiom R♭ alone [13, Theorem 7.14]
(gist.RealCohesion.CrispFunctionsAreContinuous): Shulman remarks that
strong extensionality of the function can replace Axiom T in his
proof, and strong extensionality follows from Axiom R♭; his
components of a crisp set are replaced by maps to 𝟚
(gist.RealCohesion.IndistinguishablePoints). So the continuity of
crisp functions, and two parts of Corollary 11.6, that the canonical
map is injective and that its values are ε-δ continuous, need neither
Axiom T nor crisp excluded middle. So does the n-variable form of
Theorem 11.5 [13, Theorem 7.17, GPT-6 Astra]
(gist.RealCohesion.CrispFunctionsOfSeveralVariables): a crisp function
of one variable obtained along a digit-interleaving curve
(gist.RealCohesion.DigitCurve) carries the one-variable theorem to n
variables, and dyadic detection reaches every nearby point. It gives
Remark 3.4 of [13] and the continuity of the values of the canonical
map ♭ (ℝⁿ → ℝ) → (♭ ℝⁿ → ♭ ℝ); and the map is injective, by rational
detection in n variables (gist.RealCohesion.FlatFunctionsOfSeveralVariables).
Under crisp excluded middle, every continuous map ♭ ℝⁿ → ♭ ℝ is a value
of that map [13, Theorem 3.3]: it is uniformly continuous on boxes at
crisp rational points (gist.RealCohesion.CrispUniformContinuityOnBoxes)
and extends by Dedekind cuts over rational boxes
(gist.RealCohesion.CrispExtensionOnBoxes); for n = 1 this gives
Corollary 11.6 in Shulman's words with crisp excluded middle for 𝓤₀.
Lemma 12.3, Theorem 12.4 and Corollary 12.5 are formalized too:
Theorem 12.4 and Corollary 12.5 for the disc, and for the ball in
every dimension, from crisp excluded middle and Axiom R♭; Lemma 12.3
from crisp excluded middle with Axiom T or with Axiom C1 (see below).

The analytic LLPO. Shulman refutes the analytic lesser limited
principle of omniscience, that every real number is ≤ 0 or ≥ 0, from
crisp excluded middle and Axiom R♭ [2, Theorem 11.7]. Axiom R♭ alone
refutes it [11, Theorem 7.10] (gist.RealCohesion.AnalyticLLPO, stated
from Axiom R♭ in gist.RealCohesion.Theorems): the plateau path through
a sequence of alternating signs makes the sets where it is ≥ 0 and
where it is ≤ 0 miss alternate plateaus, which the finite-chain lemma
forbids.

Sequential hitting. GPT-6 Astra's sequential hitting holds for
functionals on X → ℝ, for any type X, from Axiom R♭ alone [11, Theorem
7.4 and the remark after it] (gist.RealCohesion.FunctionalHitting,
stated from Axiom R♭ in gist.RealCohesion.Theorems): a plateau path
through each of the sequences reduces it to sequential hitting for
functions of one variable. Hence closed half-lines are sequentially
closed, which is the form that the planned proof of Corollary 3.7 on
the cube uses [12, Part C].

Strong extensionality. Under Axiom R♭ alone, every function
f : ℝ → ℝ, crisp or not, is strongly extensional: if f u and f v are
apart, then so are u and v [13, Lemma 7.12]
(gist.RealCohesion.StrongExtensionality, and the target
Target-strong-extensionality in gist.RealCohesion.Theorems). Sequential
hitting along points that move from u towards v by shrinking clamped
steps finds a step at which f is still apart from f v, and locatedness
of v - u then separates u and v. Shulman remarks after his Theorem
11.5 that strong extensionality of f can replace both of its uses of
Axiom T. Rational detection also holds in n variables: a function
ℝⁿ → ℝ that is positive somewhere is positive at a rational point
(gist.RealCohesion.RationalDetection, and Target-7-6-in-dimension), by
induction on n.

Bolzano–Weierstrass. Under crisp excluded middle, every crisp sequence
of rational points of the cube [-1,1]ⁿ has a strictly increasing crisp
sequence of indices along which it converges, with modulus 2⁻ⁱ in the
supremum norm, to a crisp point of the cube [11, Lemma 3.6]
(gist.RealCohesion.CrispBolzanoWeierstrass). Crisp excluded middle
decides, at every box with rational corner and side, whether the
sequence visits it arbitrarily late, because boxes are finite data
with crisp representatives. The bisection is
gist.RealCohesion.CrispBisection, for any crisp family of propositions
on boxes; with the family of boxes on which the values of a continuous
map spread, it gives uniform continuity on boxes
(gist.RealCohesion.CrispUniformContinuityOnBoxes).

The grid and Kuhn's lemma. For a crisp map F from ℝⁿ to the cube, crisp
excluded middle labels every point of the grid of level m, of side 2ᵐ,
with n bits [11, proof of Corollary 3.7]: the i-th bit is ₀ on the face
where the i-th coordinate is -1, ₁ on the face where it is 1, and ₀ or
₁ elsewhere according as F does not or does move that coordinate down.
A ₀ gives u_i ≤ F_i(u) and a ₁ gives F_i(u) ≤ u_i
(gist.RealCohesion.CubeGrid). Kuhn's cubical lemma, in the form of
Isabelle's kuhn_lemma, then gives a unit cube of the grid on which
every bit takes both values. It is proved in dimensions 0, 1 and 2,
the last by a parity count of the triangles of the grid
(gist.RealCohesion.KuhnLemma), and in every dimension by Harrison's
route: the simplices of a cube are given by codes, neighbouring
simplices by moves that cancel their terms in pairs, and the count is
carried from dimension n to dimension n + 1 through the face where the
last coordinate is N (gist.RealCohesion.KuhnCounting and
gist.RealCohesion.KuhnLemmaGeneral).

The crisp fixed point. Under crisp excluded middle and Axiom R♭, if
Kuhn's lemma holds in dimension n, every crisp self-map of the cube
[-1,1]ⁿ has a fixed point, and every self-map f of the cube satisfies
♯ ∃ x , f x ＝ x [11, Corollary 3.7, for the cube]
(gist.RealCohesion.CubeFixedPoint, and Target-3-7-crisp and
Target-3-7-sharp in gist.RealCohesion.Theorems). At every level the
labels give a unit cube of the grid on which every bit takes both
values; Bolzano–Weierstrass gives a limit of the base corners along a
subsequence; and as closed half-lines are sequentially closed, the map
fixes the limit. As Kuhn's lemma is proved in every dimension, both
forms hold outright in every dimension; dimension 2 is the case of
Shulman's Theorem 12.4 and Corollary 12.5, for the square. Corollary
3.7 itself is stated for the Euclidean ball, a crisp retract of the
cube, to which both forms pass (gist.RealCohesion.BrouwerStatements);
the retraction x ↦ x / max(1 , ‖x‖²) needs multiplication and division
of real numbers, but no square roots (gist.RealCohesion.EuclideanBall).
A fixed
point is an approximate fixed point, so the crisp form also gives the
cube form of Shulman's Theorem 12.6 from crisp excluded middle and
Axiom R♭, the starter target Target-12-6-cube-from-LEM of the second
addendum, outright in every dimension.

Approximate fixed points. Under crisp excluded middle and Axioms R♭
and T, if Kuhn's lemma holds in dimension n, every self-map f of the
cube, crisp or not, has rational approximate fixed points: for every
rational ε > 0 there is a rational point q of the cube with
|f q - q| < ε in the supremum norm [11, Theorem 4.3, for the cube]
(gist.RealCohesion.ApproximateCubeFixedPoint, and Target-4-3 in
gist.RealCohesion.Theorems). For crisp f, sequential hitting at the
crisp fixed point finds a grid point where the margin of f is
positive. Axiom T then makes that existence codiscrete, because, for
every sequence of real numbers, the proposition that some term is
positive is codiscrete under Axiom T [11, Lemma 4.1]
(gist.RealCohesion.PositiveTerms and AxiomTObstruction), and
Shulman's decrispification passes from crisp maps to all maps. As
Kuhn's lemma is proved in every dimension, this holds outright. Also under crisp
excluded middle and Axiom T, two real numbers that are not equal are apart,
which is Shulman's Theorem 8.32 without his Axiom C1
(gist.RealCohesion.AnalyticMarkovObstruction and AxiomTObstruction).

The modules:

 * gist.RealCohesion.OvertConnectedness: the sets 𝟚-mod P, overt
   connectedness, and the approximate intermediate value theorem for
   TypeTopology's Dedekind reals from the nullness of the 𝟚-mod P.

 * gist.RealCohesion.CrispDiscreteness: under axiom C1, the counit of
   ♭ is an embedding on crisp sets [2, Theorem 8.21] and 𝟚-mod P is
   ♭-discrete for crisp P; with the discrete axiom of choice this
   gives crisp excluded middle; under Axiom R♭, Shulman's Theorems
   11.3 and 11.4; and the analytic Markov principle for crisp reals.

 * gist.RealCohesion.ShapeProducts: products of types with
   contractions are connected, for any modality.

 * gist.RealCohesion.ShapeContinuity: for a reflective subuniverse,
   the countable continuity comparison κ, the zero-shape, and the
   effectivity of set truncation.

 * gist.RealCohesion.RealPathQuotient: the set quotient of a type by
   the paths from an interval, its iterates and their naturality.

 * gist.RealCohesion.CrispCountableChoice: countable choice for crisp
   families of arbitrary types.

 * gist.RealCohesion.ContinuityObstruction: if two crisp sequences
   have coordinatewise equal zero-shapes but distinct zero-shapes,
   countable choice for crisp families refutes continuity.

 * gist.RealCohesion.FiniteHeightContinuity: the finite-height
   principle, unbounded depth, and the conditional refutation of
   countable continuity for the tagged sum of the tower.

 * gist.RealCohesion.RealShapeContinuity: the real-cohesive instance,
   for a reflection onto the ℝ-null types with real paths, and the
   identification of its modal crisp types with the ♭-discrete ones
   under Axiom R♭.

 * gist.RealCohesion.Cylinders: frames with a system of cylinders
   have no points, and the uniform-level lemma behind the failure of
   the fan theorem; and following a branch of binary words, shared
   with gist.RealCohesion.BinaryBarObstruction.

 * gist.RealCohesion.PointlessEnd: an abstract version of the frames
   of the locales X_e, as an Artin gluing, with its points, the
   collar, connectedness, the coordinate map, and the failure of the
   fan theorem at the level of frames.

 * gist.RealCohesion.CohenFrame: the frame of regular open sets of the
   binary tree, a nontrivial frame with a cylinder system, so that the
   hypotheses on the pointless end can be met constructively.

 * gist.RealCohesion.PointlessEndExample: an instance of all the
   hypotheses of gist.RealCohesion.PointlessEnd, with a one-point
   space in place of the open interval, showing that they are
   consistent.

 * gist.RealCohesion.BinaryBarObstruction: splitting bars, the
   double-negated empty word from the sibling cover, the empty word
   from uniformity, and the conditional refutation of the full fan
   theorem.

 * gist.RealCohesion.BinaryBarFrame: the frame-level forms of the
   binary-bar conditions B1–B3 for the bar of
   gist.RealCohesion.PointlessEnd.

 * gist.RealCohesion.AnalyticMarkovObstruction: the analytic Markov
   principle, its equivalence with the stability of positivity and
   with its form for apartness, the dense positive family, the five binary-bar
   conditions B1–B5, and the conditional refutations of the analytic Markov
   principle and the full fan theorem.

 * gist.RealCohesion.CrispBarObstruction: the obstructions with crisp
   data, and, under crisp excluded middle, the positivity of a dense
   family at crisp elements.

 * gist.RealCohesion.Sharp: the modality ♯ as a record of
   assumptions, codiscreteness, and Shulman's Theorem 3.3.

 * gist.RealCohesion.NativeSharp: that record instantiated with the
   native ♯ of gist.CohesiveApartness.Sharp, so that its four fields
   are definitions.

 * gist.RealCohesion.AxiomTObstruction: under crisp excluded middle,
   codiscrete propositions are stable under double negation, so
   Axiom T gives the analytic Markov principle, also for apartness
   (Shulman's Theorem 8.32 without Axiom C1), and the obstructions
   refute it. Also Lemma 4.1 of the write-up: under Axiom T, that some
   term of a sequence of real numbers is positive is codiscrete.

 * gist.RealCohesion.PositiveTerms: for every sequence of real
   numbers, a real number that is positive exactly when some term
   is, the real-analytic part of Lemma 4.1 of the write-up.

 * gist.RealCohesion.ReflectionMaps: the action of a reflection on
   maps, shared by gist.RealCohesion.ShapeContinuity and
   gist.RealCohesion.BooleanCocycleObstruction; and two facts about
   types with contractible reflection, shared by
   gist.RealCohesion.ShapeProducts, BooleanCocycleObstruction and
   RealSubsetShape.

 * gist.RealCohesion.RealNull: the ℝ-null types, and, for a
   reflection onto them, that under Axiom R♭ its crisp modal types
   are the ♭-discrete ones and maps from ℝ to modal types are constant.

 * gist.RealCohesion.BooleanCocycleObstruction: for a reflective
   subuniverse, if a surjection q : X → T onto a set carries a
   nontrivial Boolean cocycle on its kernel, ○ X is contractible, the
   type of two-element types is modal and every map X → 𝟚 is
   constant, then ○ T is not a set.

 * gist.RealCohesion.RealPathDescent: unique Boolean real-path
   descent, as an assumption, and its use.

 * gist.RealCohesion.RealKernelCocycle: the zero indicator on the
   crisp points of the kernel of a crisp g : ℝ → ℝ, and, assuming its
   invariance along real paths, the Boolean cocycle on the kernel
   obtained by descent, with its cocycle law by uniqueness.

 * gist.RealCohesion.CrispDecisions: Boolean values of decisions by
   crisp excluded middle.

 * gist.RealCohesion.CrispRationals: every natural number, integer and
   rational number, every list of such, and every function from Fin n
   to them, for crisp n, is equal to a crisp one. So crisp excluded
   middle decides crisp families of propositions on these types at
   every point (crisp elimination). Also, given crisp-ap-^♭ and the
   ♭-discreteness of crisp propositions, the counit of ♭ is an
   embedding on crisp sets [2, Theorem 8.21], for
   gist.RealCohesion.CrispDiscreteness and FiniteChainDiscreteness. It
   re-exports gist.RealCohesion.FinVectors.

 * gist.RealCohesion.ApproximateBrouwerDisc: Shulman's Theorem 12.6
   for the round disc, for every real ε > 0 and for every rational
   ε > 0, from univalence and Axiom R♭, through the square and the
   retraction onto the disc, which does not increase Euclidean
   distances between any two real points.

 * gist.RealCohesion.ApproximateBrouwerSquare: Shulman's Theorem 12.6
   for the square, from univalence and Axiom R♭, as the target
   Target-12-6-cube: the classifying type of 𝟚 collapsed along a crisp
   proposition is ℝ-null, and a family over the plane built from the
   double cover forces the crisp proposition that some point is moved
   by little.

 * gist.RealCohesion.BoundaryRetractionFromC1 (Claude Fable 5.2):
   Shulman's Lemma 12.3 for the square, and for the cube relative to
   Kuhn's lemma, from crisp excluded middle and Axiom C1 (GPT-6
   Astra's theorem); either ℝ is ♭-discrete, or no self-map of the cube
   is fixed-point free; and the fixed-point theorems for the cube from
   crisp excluded middle, C1 and "ℝ is not ♭-discrete".
   gist.RealCohesion.BoundaryRetractionFromC1Statements states them with
   their types written out, and derives the hypotheses from Axiom R♭;
   gist.RealCohesion.BoundaryRetractionFromC1Targets derives the targets
   Target-3-7-crisp and Target-3-7-sharp from them, and gives the
   fixed-point theorems with C1 as an ordinary hypothesis.

 * gist.RealCohesion.Collapse: a type collapsed along a proposition,
   the quotient of X + Q by "equal, or Q"; it is contractible under Q,
   reflects identifications up to Q, and respects equivalences.

 * gist.RealCohesion.CrispExactIVTFromTotalOrder (Claude Fable 5.2):
   the exact intermediate value theorem for crisp functions, without
   Axiom T, from a choice of x ≤ y or y ≤ x for crisp reals, which
   follows from the decidability of their order and so from crisp
   excluded middle for 𝓤₀; with the continuity of crisp functions at
   crisp points as a hypothesis.

 * gist.RealCohesion.CrispQuotients: a crisp quotient of a ♭-discrete
   type is ♭-discrete, if crisp propositions are (Shulman's Lemma
   8.24).

 * gist.RealCohesion.DiscreteConnectedTypes (Claude Fable 5.2): a crisp
   type whose points are merely equal to a crisp point and whose
   identity types between crisp points are ♭-discrete is ♭-discrete;
   with crisp identity induction from the native ♯.

 * gist.RealCohesion.DiscreteSets (Claude Fable 5.2): Shulman's Lemma
   8.15 with its scope. Decidable equality gives ℝ-nullity, from the
   constancy of maps ℝ → 𝟚; under crisp excluded middle and Axiom R♭ a
   crisp ℝ-null set has decidable equality; and that fails for sets
   that need not be crisp.

 * gist.RealCohesion.FinVectors: functions on Fin n as vectors, with a
   new first entry, in a module without --cohesion; and choice over
   Fin n for propositional truncations.

 * gist.RealCohesion.RationalPoints: abstract copies of the embedding
   ℚ → ℝ and of 0ℝ, which keep type checking fast.

 * gist.RealCohesion.RationalArithmetic, RationalLimits and
   RationalLipschitz: rational arithmetic, halving sequences, multiples
   of a rational unit and the bounds of halving sequences by powers of
   2/3, monotone sequences, and 1-Lipschitz rational functions.

 * gist.RealCohesion.NestedIntervals: the real number determined by
   nested rational intervals.

 * gist.RealCohesion.CrispConnectedness: a crisp predicate that is
   open and co-open at the crisp points of a rational interval holds
   at one end if and only if it holds at the other, by bisection with
   crisp excluded middle.

 * gist.RealCohesion.RealOrder and CrispRealAnalysis: signs of real
   numbers; the continuity of crisp real functions at crisp points, as
   an assumption, Crisp-Real-Continuity, which
   gist.RealCohesion.CrispContinuity now proves; and the analysis of
   crisp functions used below: separation, and paths that cannot leave
   0.

 * gist.RealCohesion.ZeroPlateauInvariant: if a crisp g : ℝ → ℝ
   oscillates at 0 and its crisp nonzero zeros lie in plateaux, its
   zero indicator is invariant along crisp real paths, from crisp
   excluded middle and the continuity of crisp functions.

 * gist.RealCohesion.LipschitzExtension: the extension of a 1-Lipschitz
   rational function to ℝ, and the transfer of bounds, flatness and
   signs to the extension.

 * gist.RealCohesion.DyadicProfile and DyadicLevels: the dyadic
   1-Lipschitz function f : ℚ → ℚ, with its plateaux and bumps.

 * gist.RealCohesion.DyadicOscillation: its extension g : ℝ → ℝ, with
   g 0 ＝ g 1 ＝ 0, oscillation at 0, the plateaux around its crisp
   nonzero zeros, and hence the invariance of its zero indicator.

 * gist.RealCohesion.RealSubsetShape: the assembly for nLab problem 1:
   the conditional core, for a crisp g whose zero indicator is
   invariant, and the concrete theorem for the dyadic g.

 * gist.RealCohesion.ApproximateIVTStatement: the statements of the
   approximate intermediate value theorem, of its normal form and of
   sequential hitting, from Fable's starter module.

 * gist.RealCohesion.FiniteChainLevels: levels, which are binary
   sequences, their adjacency, and that a chain of n adjacent levels
   from the zero level ends in a level with a 0 at position n.

 * gist.RealCohesion.FiniteChainQuotient: the quotient Q of levels by
   finite chains, a large quotient, which is effective, so that a
   level in the class of the zero level has a 0 somewhere.

 * gist.RealCohesion.FiniteChainDiscreteness: under Axiom R♭, if 𝟚 is
   ♭-discrete then so is Q, and every map ℝ → Q is constant.

 * gist.RealCohesion.FiniteChainLemma: the finite-chain lemma. If
   every map ℝ → Q is constant, two predicates that cover ℝ and miss
   alternate plateaus force a monotone depth c : ℕ → 𝟚 to take the
   value ₁.

 * gist.RealCohesion.RealLattice: max, min and clamps of real numbers,
   and abstract copies of TypeTopology's addition and negation, with
   their order properties, and the positivity of sums, differences,
   maxima and minima, and of finite minima.

 * gist.RealCohesion.RealLimits: closeness of real numbers, limits of
   sequences with a geometric modulus, and clamped steps.

 * gist.RealCohesion.SequentialHitting: sequential hitting (GPT-6
   Astra). If every map ℝ → Q is constant, 1 ≤ h a and z converges to
   a, then h is positive at some z k, for any function h : ℝ → ℝ. Its
   path is the plateau path of gist.RealCohesion.PlateauPath.

 * gist.RealCohesion.SoftBisection: soft bisection with a gate, its
   two-case conclusion by sequential hitting, and the normal form of
   the approximate intermediate value theorem.

 * gist.RealCohesion.ApproximateIVTReduction: the reduction of the
   theorem to its normal form.

 * gist.RealCohesion.ApproximateIVT: the approximate intermediate value
   theorem, its normal form and sequential hitting, from Axiom R♭ and
   the ♭-discreteness of 𝟚.

 * gist.RealCohesion.RationalEnumeration: an enumeration of ℚ, and
   rational witnesses of decidable properties as functions of the
   data, by least-witness search.

 * gist.RealCohesion.IntervalHitting: interval hitting. If every map
   ℝ → Q is constant and u < f a < v, then u < f (z j) < v for some
   term z j of any sequence converging to a with a geometric modulus,
   for any function f : ℝ → ℝ.

 * gist.RealCohesion.CrispContinuity: under crisp excluded middle and
   the constancy of maps ℝ → Q, rational approximations of crisp
   reals, sequential continuity of crisp functions, and
   Crisp-Real-Continuity.

 * gist.RealCohesion.CrispExactIVT: Shulman's Theorem 11.2 for crisp
   witnesses, from crisp excluded middle and the constancy of maps
   ℝ → Q; and crisp rational witnesses of f a < c and of c < f b at
   arbitrary points a and b.

 * gist.RealCohesion.Quantizers: Astra's staircase quantizers, as
   finite sums of clamps. At each scale their values at a real number
   near 1/2 are close to it, and merely one of the two is rational.

 * gist.RealCohesion.PairHitting: sequential hitting along a pair of
   sequences, for a function of two real variables: the instance
   X = 𝟚 of gist.RealCohesion.FunctionalHitting.

 * gist.RealCohesion.RationalDetection: rational detection (GPT-6
   Astra). If every map ℝ → Q is constant and h x > 0 for some real x,
   then h q > 0 for some rational q, for any function h. Also the
   approximate intermediate value theorem with a rational witness, and
   rational detection in n variables.

 * gist.RealCohesion.CrispFunctionsEverywhere: Shulman's Theorem 11.5
   at crisp points with respect to all nearby points, and Theorem 11.2
   for arbitrary witnesses, from crisp excluded middle and the
   constancy of maps ℝ → Q.

 * gist.RealCohesion.RealBalls: closeness of real numbers, which is
   TypeTopology's rational balls without a proof of positivity;
   closeness from common intervals and bounds from closeness, the
   triangle inequality, balls inside rational intervals, and rational
   points near a real number.

 * gist.RealCohesion.CrispUniformContinuity: ε-δ continuity of maps
   ♭ ℝ → ♭ ℝ; and, under crisp excluded middle, their uniform
   continuity on rational intervals, by the connectedness of crisp
   rational intervals, and small oscillation around every real number.

 * gist.RealCohesion.CrispExtension: the extension of a crisp ε-δ
   continuous map ♭ ℝ → ♭ ℝ to a crisp function ℝ → ℝ, by Dedekind
   cuts, which agrees with it at crisp points.

 * gist.RealCohesion.FlatRealFunctions: Shulman's Corollary 11.6
   without Axiom T. The canonical map ♭ (ℝ → ℝ) → (♭ ℝ → ♭ ℝ) is an
   embedding, by Axiom R♭ and rational detection, and under crisp
   excluded middle its image consists of the ε-δ continuous maps; so
   ♭ (ℝ → ℝ) is equivalent to the type of ε-δ continuous maps.

 * gist.RealCohesion.BrouwerStatements: Claude Fable 5.2's starter
   module for the blueprint addendum [12]: the statements of Theorem
   7.10, Corollary 3.7, Theorem 4.3 and Theorem 8.32 of the write-up
   [11], as targets.

 * gist.RealCohesion.PlateauPath: the plateau path through an
   arbitrary sequence converging to a point, with its plateau identity
   and its value at 0. It is the path of sequential hitting, of the
   analytic LLPO and of sequential hitting for functionals.

 * gist.RealCohesion.AnalyticLLPO: Shulman's Theorem 11.7 without
   crisp excluded middle, from the constancy of maps ℝ → Q.

 * gist.RealCohesion.Plateaus: the heights, parity and plateaus shared
   by gist.RealCohesion.SequentialHitting,
   gist.RealCohesion.PlateauPath and the modules built on them.

 * gist.RealCohesion.FunctionalHitting: sequential hitting for
   functionals on X → ℝ, for any type X, and Theorem 7.4 of the
   write-up for ℝⁿ, from the constancy of maps ℝ → Q, by plateau paths
   through the sequences; and closed half-lines are sequentially
   closed.

 * gist.RealCohesion.CrispBisection: bisection of rational boxes,
   guided by crisp excluded middle, for a crisp family of propositions
   on boxes: the nested boxes, their crisp limit point, and the
   pigeonhole argument. Bolzano–Weierstrass and the uniform continuity
   of continuous maps on boxes are its instances.

 * gist.RealCohesion.CrispBolzanoWeierstrass: Lemma 3.6 of the
   write-up, Bolzano–Weierstrass for crisp sequences of rational
   points of the cube, under crisp excluded middle.

 * gist.RealCohesion.KuhnStatement: the statement of Kuhn's cubical
   lemma, which gist.RealCohesion.KuhnLemma and
   gist.RealCohesion.BrouwerStatements name by typed aliases. It uses
   neither real numbers nor modalities and contains no proof.

 * gist.RealCohesion.KuhnLemma: Kuhn's cubical lemma, stated in
   gist.RealCohesion.KuhnStatement, and proved for n = 0, 1 and 2, the
   last from function extensionality. It uses neither real numbers nor
   modalities.

 * gist.RealCohesion.KuhnCounting: sums modulo 2 over lists without
   repetitions; the cancellation lemma, by which terms paired by an
   involution without fixed points among the terms of weight 1 cancel
   in pairs; the pigeonhole principle; the general form of the count of
   the doors of one simplex; and the sums over functions on Fin n that
   Kuhn's lemma in every dimension needs. It uses neither real numbers
   nor modalities.

 * gist.RealCohesion.KuhnLemmaGeneral: Kuhn's cubical lemma in every
   dimension, from function extensionality, by Fable's route: reduced
   labels, codes of simplices, the moves between neighbouring
   simplices, the cancellation of their terms, and the induction on the
   dimension through the face where the last coordinate is N. It uses
   neither real numbers nor modalities.

 * gist.RealCohesion.RationalGrid: the rational grid of the cube, of
   level m: its side, its mesh and its grid points, in a module without
   parameters.

 * gist.RealCohesion.CubeGrid: the labels of the grid for a crisp map
   into the cube, under crisp excluded middle, with their properties
   on the faces and the two inequalities. It re-exports
   gist.RealCohesion.RationalGrid.

 * gist.RealCohesion.CubeFixedPoint: Corollary 3.7 of the write-up for
   the cube, relative to Kuhn's lemma: under crisp excluded middle and
   the constancy of maps ℝ → Q, every crisp self-map of the cube has a
   fixed point.

 * gist.RealCohesion.ApproximateCubeFixedPoint: Theorem 4.3 of the
   write-up for the cube, relative to Kuhn's lemma: under crisp
   excluded middle, the constancy of maps ℝ → Q and Axiom T, every
   self-map of the cube has rational approximate fixed points.

 * gist.RealCohesion.ShulmanWeakeningsStatements: Claude Fable 5.2's
   starter module for the second addendum [14]: statements of
   Shulman's results in his words, and of their weakenings, as
   targets.

 * gist.RealCohesion.StrongExtensionality: Lemma 7.12 of the write-up
   [13]: if every map ℝ → Q is constant, every function ℝ → ℝ is
   strongly extensional.

 * gist.RealCohesion.ContinuityForms: three forms of continuity at a
   point, by rational intervals, by rational balls and by strict
   inequalities, and their equivalence.

 * gist.RealCohesion.IndistinguishablePoints: Lemma 7.13 of the
   write-up [13], for subsets of ℝ: under Axiom R♭, if crisp U and V
   cover ℝ, a ∈ U and V has a point, then some point of U ∩ V is
   separated from a by no map U → 𝟚.

 * gist.RealCohesion.CrispFunctionsAreContinuous: Shulman's Theorem
   11.5 from Axiom R♭ alone, Theorem 7.14 of the write-up [13]: crisp
   functions are continuous at crisp points, the nearby points being
   arbitrary.

 * gist.RealCohesion.DigitCodes and DigitCells: the rational arithmetic
   of GPT-6 Astra's digit-interleaving curve, in modules without
   parameters: the two branches of the ternary shift, blocks and their
   contraction, binary digits and their weighted sums, codes of
   rational vectors, the centre 1/4, and the cells around 1/3 and 2/3.

 * gist.RealCohesion.DigitCurve: the curve P : ℝ → ℝ^m of Lemma 7.16
   of the write-up [13], its values at codes and at the centre, and
   detection along the curve.

 * gist.RealCohesion.CrispFunctionsOfSeveralVariables: the n-variable
   form of Shulman's Theorem 11.5 from Axiom R♭ alone, Theorem 7.17 of
   the write-up [13] (GPT-6 Astra).

 * gist.RealCohesion.CrispUniformContinuityOnBoxes: under crisp
   excluded middle, a crisp continuous map ♭ ℝⁿ → ♭ ℝ is uniformly
   continuous on boxes at crisp rational points, by the bisection of
   gist.RealCohesion.CrispBisection, and has small oscillation around
   every real point.

 * gist.RealCohesion.CrispExtensionOnBoxes: the extension of a crisp
   continuous map ♭ ℝⁿ → ♭ ℝ to a crisp function ℝⁿ → ℝ, by Dedekind
   cuts over rational boxes, which agrees with it at crisp points.

 * gist.RealCohesion.CrispFinitePowers: functions on Fin n with values
   in a type with crisp representatives have crisp representatives,
   for every crisp n, with no default value (the general form of gate
   G9 of the blueprint addendum [12]), by induction on the crisp n
   derived from the ♭-discreteness of ℕ, which
   gist.CohesiveApartness.CrispInduction proves from the native ♯.

 * gist.RealCohesion.FlatFunctionsOfSeveralVariables: the canonical map
   ♭ (ℝⁿ → ℝ) → (♭ ℝⁿ → ♭ ℝ) is injective, from Axiom R♭ alone, the
   first part of Theorem 3.3 of the write-up [13]; and, under crisp
   excluded middle, every continuous map is a value, the third part.

 * gist.RealCohesion.RationalBoxExtension: the extension to ℝⁿ of a
   function known at the sample points of rational boxes, by Dedekind
   cuts, given small oscillation; it is continuous and agrees with the
   given values. Continuous functions that agree at rational points
   agree everywhere, and continuous functions that are ordered at
   rational points are ordered everywhere, as are those ordered at the
   rational points of a box around a point, at that point.
   gist.RealCohesion.CrispExtensionOnBoxes is an instance.

 * gist.RealCohesion.RationalProducts: bounds for products of
   rationals in small boxes, and the facts on rational squares and
   reciprocals that the square root and the inverse use, without module
   parameters.

 * gist.RealCohesion.RealMultiplication: the product of real numbers,
   the continuous extension of the product of rationals (TypeTopology's
   DedekindReals.Multiplication is unfinished at the commit we use).
   It agrees with the product of rationals; products and sums of
   continuous functions are continuous; the laws of a commutative ring
   hold, with TypeTopology's addition; products of positive reals are
   positive, and squares are nonnegative; and the cuts of a square are
   given by intervals around the real.

 * gist.RealCohesion.RealReciprocal: the reciprocal of max(1 , s) for
   real s, the continuous extension of its rational version; it is at
   most 1, it is 1 where s ≤ 1, and s / max(1 , s)² ≤ 1. Scaled, it
   gives the inverse of every positive real number, which is unique and
   nonnegative.

 * gist.RealCohesion.RealAlgebra: the group laws of the addition, its
   strict monotonicity, and the ring identities of the sphere: the
   expansion of (x + t y)² and the completion of the square.

 * gist.RealCohesion.RealSquareRoot: the square root of a real number,
   by cuts, transcribed from agda-unimath (see the disclosure above);
   it is nonnegative, its square is x for x ≥ 0, nonnegative square
   roots are unique; and products of nonnegative reals are nonnegative.

 * gist.RealCohesion.EuclideanBall: finite sums of reals, the squared
   norm, and the Euclidean ball Dⁿ = {x : ℝⁿ | ‖x‖² ≤ 1}, which lies in
   the cube; the retraction x ↦ x / max(1 , ‖x‖²) of ℝⁿ onto it, so
   that Dⁿ is a retract of the cube; the retraction is nonexpansive,
   and approximate fixed points on the cube give approximate fixed
   points on the ball.

 * gist.RealCohesion.DoubleCover: the double cover of the punctured
   plane given by four half-planes, trivial over each and twisted once
   around the origin.

 * gist.RealCohesion.SquareEstimates: the estimates on the plane for
   Shulman's Theorem 12.6 for the square: margins, clamps, the four
   lines, and the step from an approximate fixed point of the modified
   map to one of the given map.

 * gist.RealCohesion.SphereRetractionFromC1 (Claude Fable 5.2):
   Shulman's Lemma 12.3 for the disc, and for the ball relative to
   Kuhn's lemma, from crisp excluded middle and Axiom C1, also in the
   two forms of gist.RealCohesion.EuclideanSphere; and the fixed-point
   theorems for the ball and the disc from crisp excluded middle, C1 and
   "ℝ is not ♭-discrete".

 * gist.RealCohesion.EuclideanSphere: the sphere
   Sⁿ⁻¹ = {x : ℝⁿ | ‖x‖² = 1}, and Shulman's Lemma 12.3 in every
   dimension from the analytic Markov principle: if some f : Dⁿ → Dⁿ
   has no fixed point, then Sⁿ⁻¹ is a retract of Dⁿ, and, in the
   literal form, the inclusion of Sⁿ⁻¹ into Dⁿ has a retraction.

 * gist.RealCohesion.RationalVectors: sums, inner products and squared
   norms of vectors of rationals, and the nonexpansiveness of the
   retraction onto the ball for rational vectors; without module
   parameters.

 * gist.RealCohesion.Theorems: the statements of
   gist.RealCohesion.FlatSplit, below, with the same names, in --safe
   mode: crisp-ap-^♭ and the ♭-discreteness of 𝟚, ℕ and ♭ ℝ come from
   the native ♯ (gist.CohesiveApartness.CrispInduction). Also the
   results of gist.RealCohesion.AxiomTObstruction for the native ♯;
   and, from Axiom R♭ alone, Shulman's Theorem 11.7 without crisp
   excluded middle, as the target Target-7-10 of
   gist.RealCohesion.BrouwerStatements, and sequential hitting for ℝⁿ
   and for functionals, with the target Target-hitting and closed
   half-lines; and Kuhn's lemma for n = 0, 1 and 2, with the type of
   gist.RealCohesion.BrouwerStatements, and the crisp fixed point on
   the cube, as the targets Target-3-7-crisp and Target-3-7-sharp and
   in dimensions 0, 1 and 2; Lemma 4.1 and Shulman's Theorem 8.32
   without Axiom C1 for the native ♯, as the targets Target-4-1 and
   Target-8-32; and approximate fixed points on the cube, as the
   target Target-4-3 and in dimensions 0, 1 and 2. Last, targets of
   gist.RealCohesion.ShulmanWeakeningsStatements: strong
   extensionality and rational detection in n variables from Axiom R♭,
   and rational detection, the exact intermediate value theorem, and
   Shulman's Theorem 11.5 and Corollary 11.6 in his words; and
   Theorem 11.5 from Axiom R♭ alone, with Crisp-Real-Continuity and two
   parts of Corollary 11.6 as corollaries; and its n-variable form from
   Axiom R♭ alone, with Remark 3.4 of the write-up and the continuity
   of the values of the canonical map in n variables, and the
   injectivity of that map; and the cube form of Shulman's Theorem 12.6
   from crisp excluded middle and Axiom R♭; and Theorem 3.3 of the
   write-up in every crisp dimension, as the target Target-3-3, with
   Corollary 11.6 in Shulman's words as the target Target-11-6; and
   Shulman's Lemma 8.15 with its scope, from gist.RealCohesion.DiscreteSets;
   and Corollary 3.7 of the write-up for the Euclidean ball, in both
   forms, with Shulman's Theorem 12.4 and Corollary 12.5 for the disc;
   and Theorem 4.3 of the write-up for the ball and for the disc; and
   Shulman's Lemma 12.3 from crisp excluded middle and Axiom T, without
   Axiom C1, in every dimension and for the disc; and Shulman's Lemma
   12.3 from crisp excluded middle and Axiom C1, without Axiom T, for
   the square and the disc and relative to Kuhn's lemma for the cube
   and the ball, with the fixed-point theorems from crisp excluded
   middle, C1 and "ℝ is not ♭-discrete" (gate G27); and Shulman's
   Theorem 12.6 for the square from univalence and Axiom R♭, as the
   target Target-12-6-cube (gate G25); and the exact intermediate value
   theorem for crisp functions from crisp excluded middle for 𝓤₀, as
   the target Target-3-5, also from weaker hypotheses; and Shulman's
   Theorem 12.6 for the round disc from univalence and Axiom R♭ (gate
   G26), for every real ε > 0 and for every rational ε > 0; and Kuhn's
   lemma in every dimension, in both forms, with which every theorem
   above that is stated relative to Kuhn's lemma also holds without it
   (the forms …-in-every-dimension, and R♭-gives-Target-12-6-cube-from-LEM).
   This module is imported here.

 * gist.RealCohesion.BooleanTests: a map into a type with decidable
   equality is constant when every map into 𝟚 is; without module
   parameters (step K4 of the consolidation [20]).

 * gist.RealCohesion.PunctualCohesion: the consequences of Axiom C1 for
   an ordinary family of pointed generators: maps from a generator to a
   ♭-discrete type are constant, and conversely; crisp propositions and
   function types into ♭-discrete types are ♭-discrete; decidable
   equality gives ♭-discreteness from that of 𝟚 (step K4). Without
   reals.

 * gist.RealCohesion.Constancy: the constancy of maps from ℝ to the
   quotient Q of levels by finite chains, the strictly rising generator
   path NC (Rising-Generator-Path), its instance for Axiom R♭, and the
   transfer lemma for sets (step K5). Without modalities.

 * gist.RealCohesion.HigherTransfer: nullness transfers along a
   normalized path and along a strictly rising map, for arbitrary
   types, and so along a merely rising generator path (W4, gates 1 and
   2). Without modalities; outside the Agda 2.8 comparison closure.

 * gist.RealCohesion.TheoremsFromC1: the forms of W1 to W4, from Axiom
   C1 for an ordinary family of generators and the propositional
   truncation of NC in place of Axiom R♭, and four statements that do
   not assume NC [20, 21, 22].

 * gist.RealCohesion.FlatSplit: crisp induction, with --flat-split.
   This is the route for Agda 2.8, which has no ♯, kept for
   comparison.
   It proves crisp-ap-^♭, the module parameter of
   gist.RealCohesion.CrispDiscreteness other than the usual
   extensionality and truncation assumptions, and instantiates that
   module. It also proves that ℕ is ♭-discrete, a port of the proof in
   agda-unimath, so that the discrete axiom of choice gives countable
   choice for crisp families, and instantiates
   gist.RealCohesion.RealShapeContinuity with it. Finally, it
   instantiates the concrete theorems of
   gist.RealCohesion.RealSubsetShape with the proof that 𝟚 is
   ♭-discrete from gist.CohesiveApartness.FlatSplit, and
   gist.RealCohesion.ApproximateIVT with that proof and crisp-ap-^♭,
   so that the approximate intermediate value theorem holds assuming
   only Axiom R♭. It restates the theorems of
   gist.RealCohesion.RealSubsetShape without their continuity
   hypothesis, and states the continuity of crisp functions and
   Shulman's Theorem 11.2 from crisp excluded middle and Axiom R♭,
   and rational detection and the approximate intermediate value
   theorem with a rational witness from Axiom R♭ alone. Last, it
   proves that ♭ A is ♭-discrete and states Shulman's Corollary 11.6
   from crisp excluded middle and Axiom R♭. Agda does not allow
   --flat-split with --safe and --without-K, so this module is not
   --safe and is not imported here. It has to be checked separately.

Colin Zwanziger's Lean formalization of results on pre-cohesive
geometric morphisms is a separate, companion development. The
Diaconescu argument in gist.RealCohesion.CrispDiscreteness is an
internal counterpart of the step in his proof that epi-continuity and
a connected codiscrete classifier force a Boolean base.

The modules here that use --cohesion make this index use it too,
because --cohesion is infective. As explained in
gist.CohesiveApartness.index, this folder is therefore not imported by
gist.index.

In the packaging release of 13 November 2026 [24], by Claude Opus 5.5,
every bibliography entry for a local note in this folder gained the
path of its file, the five new modules of the consolidation were added
to the list above, and some prose was made precise; no code changed.
The references/ identifiers below refer to the project's research
archive. The public repository gives the theorem statements, proof
status and source attributions in docs/shulman.md and docs/sources.md.

[1] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, draft of 25 October 2026, revised
    10 November 2026 with the same theorem numbers.
    references/C02-write-up-2026-11-10.tex

[2] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3

[3] An ordinary real-cohesive countermodel to countable-power
    continuity. Research notes, 25 October 2026.
    references/C05-ordinary-countermodel.txt

[4] An informal higher-topos countermodel and its internal
    obstruction. Research notes, 25 October 2026.
    references/C07-higher-topos-countermodel.txt

[5] Internal real-path quotients and the finite-height principle.
    Research notes, 25 October 2026.
    references/C06-internal-real-path-quotients.txt

[6] The libraries PointlessEnd, RealContinuity, InternalHeight and
    ContinuityChoice of the Lean package cohesion, 25–27 October 2026,
    with their reports NLAB23.md, REALCONTINUITY.md and
    CONTINUITYCHOICE.md.
    references/C10-NLAB23.md
    references/C10a-REALCONTINUITY.md
    references/C10b-CONTINUITYCHOICE.md

[7] The approximate intermediate value theorem from real cohesion
    alone. Proof note by Claude Fable 5.2, revision 2, 10 November
    2026, audited by GPT-6 Astra.
    references/F17-aivt-proof-rev2.md

[8] Formalization blueprint, revision 3, and handoff, package
    revision 4: the approximate IVT from Axiom R♭. Claude Fable 5.2,
    10 November 2026.
    references/F15-aivt-blueprint-rev3.md
    references/F16-aivt-handoff-rev4.md

[9] GPT-6 Astra. Positive rational detection, 10 November 2026: §1,
    sequential hitting, and §§2–3, rational detection; and audits of
    [7], of sequential hitting and of the step from sequential hitting
    to the theorem, 10 November 2026.
    references/A11-positive-rational-detection.txt

[10] Fable. Shulman's stated questions: three updates, Part A, Axiom T
     is not needed in §§11–12. Working note, 10 November 2026,
     audited by GPT-6 Astra.
     references/F18-shulman-three-updates.md

[11] Answers to some open problems in real-cohesive homotopy type
     theory. Research notes, seventh revision of 11 November 2026.
     references/C03-write-up-2026-11-11-seventh.tex
     references/C03a-write-up-seventh-README.txt

[12] Formalization blueprint, addendum: Theorem 7.10, Corollary 3.7,
     Theorem 4.3 and Theorem 8.32, revision 4. Claude Fable 5.2,
     11 November 2026.
     references/F14-brouwer-addendum-rev4.md

[13] Answers to some open problems in real-cohesive homotopy type
     theory. Research notes, revision of 12 November 2026, with the
     new Subsection 7.5 and the earlier numbers unchanged.
     references/C04-write-up-2026-11-12.tex

[14] Second addendum to the formalization plan: Shulman's statements
     and their weakenings, revision 4. Claude Fable 5.2, 12 November
     2026.
     references/F13b-second-addendum-rev4-as-amended.md
     Gate G27, cited above with revision 5, is not in revision 4; it
     was added in revision 5, which is retained only as revision 6,
     whose header records that change:
     references/F13-second-addendum-rev6.md

[15] The agda-unimath library, https://github.com/UniMath/agda-unimath,
     commit 7551865. MIT licence; a copy is LICENSE-agda-unimath.md in
     this folder.

[16] Claude Fable 5.2. Note: Shulman's approximate Brouwer theorem (12.6)
     without the shape modality. Revision 2, 12 November 2026, audited
     by GPT-6 Astra.
     references/F11-shulman-12-6-rev2.md

[17] Claude Fable 5.2. Kuhn's lemma in every dimension: the finite
     route. Revision 3, 13 November 2026, audited by GPT-6 Astra.
     references/F10-kuhn-finite-route-rev3.md

[18] Brouwer_Fixpoint.thy of Isabelle/HOL (src/HOL/Analysis), at
     revision 87958a2e5f99606413f8c4f3af90935a5ac33110 of the Isabelle
     mirror, by John Harrison, translated from HOL Light by Robert
     Himmelmann, with LCP. BSD three-clause licence; a copy is
     ISABELLE-COPYRIGHT in this folder.

[19] Claude Fable 5.2. Final audit: the Shulman / real-cohesion
     formalization and the Orbifolds targets T1–T5b, 13 November 2026,
     Sections 7 and 9 (findings and repair plan).
     references/F09-final-audit.md

[20] Claude Fable 5.2. Plan: consolidation of r3, and "C1 + NC in place
     of R♭" (G27(d)), 13 November 2026, Section 2 (steps K1 to K6),
     Section 4 (W1 to W4) and Section 5 (decision D2).
     references/F02-consolidation-plan.md

[21] Claude Fable 5.2. Addendum 01 to the consolidation plan,
     13 November 2026.
     references/F03-consolidation-plan-addendum-01.md

[22] GPT-6 Astra. Consolidation implementation, second release,
     13 November 2026, with the W3/W4 acceptance inventory and the W4
     independent mathematical review of the same day.
     references/A27-consolidation-release-02.txt

[23] GPT-6 Astra. Gameplan for Opus: a subset of the Dedekind reals
     whose shape is not a set, 25 October 2026.
     references/A32-subset-shape-gameplan.md

[24] GPT-6 Astra. Portable local packaging, release 04
     (OPUS-CONSOLIDATION-RELEASE-04), 13 November 2026, which relays
     the documentation findings F1 to F7 of Claude Fable 5.2's sealed
     review of the consolidation.
     references/A37-consolidation-release-04.txt

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

module gist.RealCohesion.index where

import gist.RealCohesion.AnalyticLLPO
import gist.RealCohesion.AnalyticMarkovObstruction
import gist.RealCohesion.ApproximateBrouwerDisc
import gist.RealCohesion.ApproximateBrouwerSquare
import gist.RealCohesion.ApproximateCubeFixedPoint
import gist.RealCohesion.ApproximateIVT
import gist.RealCohesion.ApproximateIVTReduction
import gist.RealCohesion.ApproximateIVTStatement
import gist.RealCohesion.AxiomTObstruction
import gist.RealCohesion.BinaryBarFrame
import gist.RealCohesion.BinaryBarObstruction
import gist.RealCohesion.BooleanCocycleObstruction
import gist.RealCohesion.BooleanTests
import gist.RealCohesion.BoundaryRetractionFromC1
import gist.RealCohesion.BoundaryRetractionFromC1Statements
import gist.RealCohesion.BoundaryRetractionFromC1Targets
import gist.RealCohesion.BrouwerStatements
import gist.RealCohesion.CohenFrame
import gist.RealCohesion.Collapse
import gist.RealCohesion.Constancy
import gist.RealCohesion.ContinuityForms
import gist.RealCohesion.ContinuityObstruction
import gist.RealCohesion.CrispBarObstruction
import gist.RealCohesion.CrispBisection
import gist.RealCohesion.CrispBolzanoWeierstrass
import gist.RealCohesion.CrispConnectedness
import gist.RealCohesion.CrispContinuity
import gist.RealCohesion.CrispCountableChoice
import gist.RealCohesion.CrispDecisions
import gist.RealCohesion.CrispDiscreteness
import gist.RealCohesion.CrispExactIVT
import gist.RealCohesion.CrispExactIVTFromTotalOrder
import gist.RealCohesion.CrispExtension
import gist.RealCohesion.CrispExtensionOnBoxes
import gist.RealCohesion.CrispFinitePowers
import gist.RealCohesion.CrispFunctionsAreContinuous
import gist.RealCohesion.CrispFunctionsEverywhere
import gist.RealCohesion.CrispFunctionsOfSeveralVariables
import gist.RealCohesion.CrispQuotients
import gist.RealCohesion.CrispRationals
import gist.RealCohesion.CrispRealAnalysis
import gist.RealCohesion.CrispUniformContinuity
import gist.RealCohesion.CrispUniformContinuityOnBoxes
import gist.RealCohesion.CubeFixedPoint
import gist.RealCohesion.CubeGrid
import gist.RealCohesion.Cylinders
import gist.RealCohesion.DigitCells
import gist.RealCohesion.DigitCodes
import gist.RealCohesion.DigitCurve
import gist.RealCohesion.DiscreteConnectedTypes
import gist.RealCohesion.DiscreteSets
import gist.RealCohesion.DoubleCover
import gist.RealCohesion.DyadicLevels
import gist.RealCohesion.DyadicOscillation
import gist.RealCohesion.DyadicProfile
import gist.RealCohesion.EuclideanBall
import gist.RealCohesion.EuclideanSphere
import gist.RealCohesion.FiniteChainDiscreteness
import gist.RealCohesion.FiniteChainLemma
import gist.RealCohesion.FiniteChainLevels
import gist.RealCohesion.FiniteChainQuotient
import gist.RealCohesion.FiniteHeightContinuity
import gist.RealCohesion.FinVectors
import gist.RealCohesion.FlatFunctionsOfSeveralVariables
import gist.RealCohesion.FlatRealFunctions
import gist.RealCohesion.FunctionalHitting
import gist.RealCohesion.HigherTransfer
import gist.RealCohesion.IndistinguishablePoints
import gist.RealCohesion.IntervalHitting
import gist.RealCohesion.KuhnCounting
import gist.RealCohesion.KuhnLemma
import gist.RealCohesion.KuhnLemmaGeneral
import gist.RealCohesion.KuhnStatement
import gist.RealCohesion.LipschitzExtension
import gist.RealCohesion.NativeSharp
import gist.RealCohesion.NestedIntervals
import gist.RealCohesion.OvertConnectedness
import gist.RealCohesion.PairHitting
import gist.RealCohesion.PlateauPath
import gist.RealCohesion.Plateaus
import gist.RealCohesion.PointlessEnd
import gist.RealCohesion.PointlessEndExample
import gist.RealCohesion.PositiveTerms
import gist.RealCohesion.PunctualCohesion
import gist.RealCohesion.Quantizers
import gist.RealCohesion.RationalArithmetic
import gist.RealCohesion.RationalBoxExtension
import gist.RealCohesion.RationalDetection
import gist.RealCohesion.RationalEnumeration
import gist.RealCohesion.RationalGrid
import gist.RealCohesion.RationalLimits
import gist.RealCohesion.RationalLipschitz
import gist.RealCohesion.RationalPoints
import gist.RealCohesion.RationalProducts
import gist.RealCohesion.RationalVectors
import gist.RealCohesion.RealAlgebra
import gist.RealCohesion.RealBalls
import gist.RealCohesion.RealKernelCocycle
import gist.RealCohesion.RealLattice
import gist.RealCohesion.RealLimits
import gist.RealCohesion.RealMultiplication
import gist.RealCohesion.RealNull
import gist.RealCohesion.RealOrder
import gist.RealCohesion.RealPathDescent
import gist.RealCohesion.RealPathQuotient
import gist.RealCohesion.RealReciprocal
import gist.RealCohesion.RealShapeContinuity
import gist.RealCohesion.RealSquareRoot
import gist.RealCohesion.RealSubsetShape
import gist.RealCohesion.ReflectionMaps
import gist.RealCohesion.SequentialHitting
import gist.RealCohesion.ShapeContinuity
import gist.RealCohesion.ShapeProducts
import gist.RealCohesion.Sharp
import gist.RealCohesion.ShulmanWeakeningsStatements
import gist.RealCohesion.SoftBisection
import gist.RealCohesion.SphereRetractionFromC1
import gist.RealCohesion.SquareEstimates
import gist.RealCohesion.StrongExtensionality
import gist.RealCohesion.Theorems
import gist.RealCohesion.TheoremsFromC1
import gist.RealCohesion.ZeroPlateauInvariant

\end{code}
