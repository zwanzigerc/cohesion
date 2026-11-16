Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026; proper finiteness (orbifold gate H1) added
12 November 2026; test squares, and pullbacks and inertia of abstract
orbifolds (orbifold gate H2), added 12 November 2026; the modality
layer, with étale maps and nullifications (orbifold gate H3), added
12 November 2026; Lemma G, microlinearity along étale maps (orbifold
gate H4), added 12 November 2026; Lemma F and Corollary F′, étale
descent (orbifold gate H5), added 12 November 2026; Theorems 5.4.9
and 5.4.1 in abstract form (orbifold gate H6) added 12 November 2026;
deloopings of groups from torsors, and Theorem 5.4.1 for groups given
by a multiplication (orbifold gate H6), added 12 November 2026; the
Rezk completion of a pregroupoid, and Theorem 5.4.9 for it (orbifold
gate H6), added 12 November 2026; finiteness under cover-properness in
abstract form (orbifold gate H7) added 12 November 2026; the smooth
line, Weil algebras by presentation, Myers's microlinearity, and the
targets T2, T3 and T4 in that form (orbifold gate H8), added
12 November 2026; the two statement bridges of gate H8 (normalized
presentations, Myers's literal infinitesimal varieties, and the
agreement of microlinearity and of nullification), after the review
dated 13 November 2026 (UTC), added 12 November 2026 (local time);
the first stage of orbifold gate H9 (the order of the smooth line,
ordinary topology, refinement of local homeomorphisms, and Lemmas A
and B), on the accepted library base
real-cohesion-agda-kuhn-general-2026-11-12, added 12 November 2026
(local time); the rest of gate H9 (the metric topology and Theorem
5.1.5, ordinary manifolds, the smooth line as one, microlinearity of
ordinary manifolds, Lemma D, cover-properness, the bridge from ordinary
charts, and the target T1), added 12 November 2026 (local time);
Dubuc–Penon compactness and properness, and the target T5a (orbifold
gate H10), added 13 November 2026 (local time); the Covering Property,
finite subcovers, orbit sets, zero-dimensional charts and the target T5b
(orbifold gate H10), added 13 November 2026 (local time); the final
repairs after the final audits (prose made precise, the type of
theorem-T5b-literal displayed, the imports sorted, and the code
reformatted to lines of at most 80 characters), 13 November 2026; the
consolidation (the dual numbers and the nilsquare contradiction shared
by T5a and T5b, and the lemmas of CrispTruncation moved to
gist/CohesiveApartness), 13 November 2026; its second part (the
consequences of Axiom C1 and the Boolean test shared with
gist/RealCohesion), 13 November 2026; its third part (cover-properness
for set-indexed covers, with the forms of T1, T5a and T5b for it, and
the scope of the statements made precise), 13 November 2026; the
packaging release (the paths of the cited notes, and the scope read
against the printed paper), 13 November 2026; the comparison of Weil
algebras with presentations (Weil gates WG1 to WG7), added 13 November
2026 (local time), and integrated here with the documentation
corrections of its release (WG8) the same night [7, 8].

Orbifolds as microlinear types: the Myers thread
------------------------------------------------

This folder formalizes, over TypeTopology, the results of
D. J. Myers's paper [1] that Colin Zwanziger fixed as the completion
scope of the Myers thread on 11 November 2026, over the adopted
five-item core [3]. The plan is Fable's roadmap, revision 2 [2]. Its
targets are

  T1  Theorem 6.3.7 in its intended scope, with cover-properness in
      place of Dubuc–Penon properness, from ordinary charts;
  T2  Theorem 6.4.1: quotients of microlinear sets by crisp finite
      groups are orbifolds;
  T3  Proposition 6.4.2: orbifolds are closed under pullback;
  T4  Definition 6.4.3 and Corollary 6.4.4: inertia types of orbifolds
      are orbifolds;
  T5  the strict comparison: Dubuc–Penon properness implies the
      replacement hypotheses of T1, and not conversely.

An orbifold is a microlinear type whose identity types are properly
finite (Definition 1.1.2 of [1], unchanged). Section 2.4 of [1], the
point constructions, stays at the level of paper proofs (Colin's
decision of 12 November) and is not formalized here.

The gates of [2] are numbered H0–H10. They are called "orbifold gates"
here, because the blueprint of 10 November uses H1, H2, ... for its
hitting lemmas.

Status. Gates H0 (environment and baseline), H1 (proper finiteness),
H2 (test squares; T3 and T4 for abstract orbifolds), H3 (the
modality layer: connected and étale maps, nullifications), H4
(Lemma G), H5 (Lemma F and Corollary F′) and H6 (Theorems 5.4.9 and
5.4.1: the Rezk completion of a pregroupoid as the image of the Yoneda
embedding, and deloopings of groups from torsors, both under
univalence), and H7 (finiteness under cover-properness, for abstract
charts: properly finite hom-sets and identity types of the Rezk
completion), and H8 (the algebraic half of the statement layer: the
smooth line with Postulate K, Weil algebras by presentation and their
spectra, microlinear types and orbifolds for these spectra; T2, T3
and T4; and the bridges to Myers's definitions in the adopted,
presentation-based reading, after the review), and H9 (ordinary
topology and manifolds, the bridge from ordinary charts, and T1,
OrdinaryEtaleGroupoids), and H10 (T5a, SmoothLineGroupoid, and T5b,
ProperEtaleGroupoids, with DubucPenon). All targets T1–T5 are
formalized, in the forms that the targets fix, with the scope stated
below. The comparison of Weil algebras with presentations, which Colin
Zwanziger commissioned afterwards, is formalized in eleven modules
(Weil gates WG1 to WG7 of Fable's plan [7]), listed last below. The
folders gist/RealCohesion and
gist/CohesiveApartness beside this one are those of the accepted
snapshot real-cohesion-agda-kuhn-general-2026-11-12, with the final
repairs and the consolidation of 13 November 2026 that their indexes
describe (up to the H8
delivery they were those of real-cohesion-agda-real-multiplication-
2026-11-12); this folder reuses their modules where they apply.

Scope of the statements, made precise in the third part of the
consolidation, 13 November 2026 [5], and read against the printed
paper [1] in the packaging release of the same day [6]. Four choices
belong to the adopted scope; they are not agreement with the printed
text of [1].

  (a) Tests. An infinitesimal variety is a pointed type that is merely
      pointed-equivalent to the spectrum of a Weil presentation
      (SmoothLine, MyersMicrolinearity). A test is a crisp pair: a
      square of such types together with a proof that it is an
      R-pushout; the square and the proof are crisp together. Reading
      Definition 4.2.11 of [1] with a crisp square and an ordinary
      proof gives a class of tests that contains this one. On paper the
      two classes agree under Axiom C1, by crisp-witnesses
      (C1Discreteness): an ordinary proof of a crisp proposition then
      gives a crisp one. That bridge is not stated or checked as a
      theorem, and the statements for Section 6.4 do not assume C1.

  (b) The word "literal" in names marks the versions that quantify
      over such pointed types in place of presentations: the literal
      results of gate H8 and the literal forms of T1, T5a and T5b. It
      does not mark the printed definitions.

  (c) The modality. Where the reflector ℑ is used, it is the
      nullification at all crisp infinitesimal varieties in the sense
      of (a), equivalently at the spectra of crisp presentations, the
      finite Weil spectra (literal-nullifications-are-nullifications),
      with the stated hypothesis that it preserves crisp pullbacks.
      This is the alternative of Remark 4.3.2 of [1]. Equivalence with
      the infinitesimal-disk modality of Definition 4.3.1 of [1] has
      not been proved.

  (d) Weil algebras. The comparison of presentations with the Weil
      algebras of Definition 4.1.1 of [1] and their Hom-spectra is
      formalized in WeilVarietiesFromLargeQuotients, for Weil algebras
      with carrier in 𝓤₁ and from propositional extensionality for all
      universes, an explicit parameter (crisp in WeilMicrolinearity),
      not obtained from the single-universe univalence of other
      modules; the reverse direction holds for Weil algebras in any
      universe, as a mere existence. It compares objects at the level
      of pointed spectra: maps of spectra induced by maps of algebras
      are constructed, by precomposition, but full faithfulness, the
      representation of arbitrary maps of spectra by maps of algebras,
      the duality of Lemma 4.2.2 and Postulate J are not claimed. The
      constructed instance of presented algebras is uniform, with
      carriers in 𝓤₁; a uniform instance with carriers in 𝓤₀, the
      optional small-quotient specialization, would use small
      quotients and is not built, although particular algebras in 𝓤₀,
      such as R-as-algebra, exist; nothing is claimed about whether
      small quotients are necessary. WeilMicrolinearity compares the
      tests of (a) with whole crisp squares of Weil varieties, each
      with its R-pushout proof; on a given subuniverse, nullification
      at the generators of (c) with nullification at whole crisp
      Weil-variety packages; and nullity at those generators with
      nullity at the spectra of crisp Weil algebras, with crisp algebra,
      augmentation and Weil proof (one way in any crisp universe of
      carriers, both ways in 𝓤₁). It constructs no reflector. The
      normalization of presentations and the comparison
      of the code-defined test predicates are formalized as before;
      normalization need not preserve the quotient algebra of the
      original presentation, so the algebra of a presentation is taken
      after normalization (WeilAlgebras).

(b) and (c) concern literal-theorem-6-4-1,
literal-theorem-6-4-1-for-groups, theorem-T1-literal,
theorem-T1-literal-for-set-indices, theorem-T5a, theorem-T5b-literal
and theorem-T5b-literal-for-set-indices, whose descriptions point here.
The finite subcover of T5b is a finite indexed list, in which an index
or an open may occur more than once, not a finite set of opens: it is
the composite of Myers's Remark 6.2.16, for crisp subsets, crisp covers
and a crisp countably indexed basis, under the module's hypotheses,
among them crisp excluded middle, in the form of merely a finite list
of indices. The proof uses the argument of Corollary 6.2.14 followed
by a crisp decision and finite witness selection, and neither
Corollary 6.2.14 nor Proposition 6.2.15 is stated separately, since
refinement subcompactness is not defined here (FiniteSubcovers). T1
has an endpoint for set-indexed covers, the
condition of the memo (theorem-T1-literal-for-set-indices,
OrdinaryEtaleGroupoids); its hypotheses include Axiom C1 for an
arbitrary family of pointed generators, which makes the chart index
♭-discrete, Postulate Exp, used only for the translation law of the
order (exp and log are not used), and univalence of the universe of
the carriers, an explicit hypothesis; it does not assume crisp
excluded middle. So it differs in three rows from the memo's
dependency table, which bounds the paper argument; the memo's revision
of 13 November 2026 says so after its table [5]. The binders of maps,
topologies and proofs, and the universe of the chart index, are as
CoverProperness and OrdinaryEtaleGroupoids state them; they are not
crisp unless said so. The release has also been checked with final Agda 2.9.0.

Modules.

  ProperFiniteness   (H1) Myers's Definition 6.1.3, first sentence:
                     decidable equality and a surjection from a subtype
                     of some Fin n. Closure under subtypes, binary
                     products and equivalence (also into a larger
                     universe, added at H7); finite types (added at
                     H8) and types that embed into
                     some Fin n are properly finite (GPT-6 Astra's
                     closure facts 1a–1c).

  TestSquares        (H2) Test squares and σ-local types: X^V₄ →
                     X^V₂ ×_(X^V₁) X^V₃ is an equivalence. Local types
                     are closed under equivalence, Σ over a local base
                     of a local family, the unit type, binary products,
                     pullbacks and inertia.

  AbstractOrbifolds  (H2) Orbifolds for an arbitrary family of test
                     squares (Myers's Definition 1.1.2 with the
                     abstract notion of microlinearity), and the
                     targets T3 and T4 in that form: pullbacks and
                     inertia types of orbifolds are orbifolds
                     (Proposition 6.4.2, Definition 6.4.3 and
                     Corollary 6.4.4). Intermediate results in the
                     sense of the roadmap: gate H8 instantiates the
                     family with the infinitesimal R-pushouts.

  Modalities         (H3) For a Σ-closed replete reflective subuniverse
                     (TypeTopology's Modal): reflections are unique; ○
                     commutes with Σ over a modal base (M3); units are
                     connected maps, connected maps are stable under
                     pullback, a connected map into a modal type is a
                     unit (M2); units are surjective if propositions are
                     modal (M1); étale maps, their fibres (those of ○f,
                     hence modal), closure under pullback and
                     composition, and maps between modal types (M4).

  Nullification      (H3) Nullification at a family of pointed types, as
                     a hypothesis on a reflective subuniverse; it is
                     then replete and Σ-closed, propositions are modal,
                     maps from generators to modal types are constant,
                     units are surjective; the generators are
                     connected, and types with decidable equality are
                     null at a pointed type whose maps to 𝟚 are
                     constant (both added at H8, the second the lemma
                     of the roadmap's Section 7.1, item 1). Since the
                     consolidation, the Boolean test is
                     gist.RealCohesion.BooleanTests.
                     (--cohesion only because is-null is in
                     gist.CohesiveApartness.Flat.)

  LemmaG             (H4) Fable's Lemma G, audited by Astra: for étale
                     f : X → Y, X^C ≃ X ×_Y Y^C for pointed connected C,
                     naturally in C; σ-locality passes from Y to X when
                     the test types are connected, and from X to Y when
                     f is moreover surjective. Modal types are local for
                     such squares. Pointed test squares as data.

  LemmaF             (H5) Fable's Lemma F, audited by Astra, and Astra's
                     Corollary F′, for any map whose kernel pair the
                     modality preserves: a surjection whose kernel-pair
                     projection is étale is étale; a surjection onto a
                     set from a modal type has modal target, when
                     propositions are modal. The canonical comparison
                     of pullbacks.

  CrispLemmaF        (H5) The printed forms: Lemma F for crisp maps of
                     crisp types and Corollary F′ for crisp surjections,
                     under the hypothesis that the modality preserves
                     crisp pullbacks (core item 4 for ℑ); F′ for
                     nullifications at pointed types.

  EtaleQuotients     (H6) Theorem 5.4.9 in abstract form: for a Rezk
                     completion given by its data (crisp y : G₀ → rG,
                     surjective, with G(x , x') ≃ (y x ＝ y x')), y is
                     étale when the source map is, and rG is microlinear
                     when G₀ is. Theorem 5.4.1 in abstract form: for a
                     crisp pointed connected type with modal loop space,
                     the point is étale, quotient maps into total spaces
                     of families are étale surjections, and microlinearity
                     passes to the total space. Intermediate results:
                     the Rezk completion and the delooping enter here
                     through their data; they are constructed in
                     RezkCompletion and Deloopings.

  Deloopings         (H6) For a group Γ given by a multiplication: BΓ,
                     the type of Γ-torsors, pointed by the trivial torsor;
                     the family of equivariant maps for a Γ-set, with
                     fibre the Γ-set over the base point; under
                     univalence (a module parameter), BΓ is connected
                     and its loop space is Γ.

  GroupQuotients     (H6) Theorem 5.4.1 for a crisp group given by a
                     multiplication, with modal carrier, acting on a
                     microlinear set: X // Γ is microlinear, through BΓ.

  RezkCompletion     (H6) Myers's Definitions 5.4.3 and 5.4.5: a
                     pregroupoid, presheaves on it, and its Rezk
                     completion, the presheaves that merely admit a
                     natural isomorphism from a representable. Under
                     univalence: identifications of presheaves are
                     natural isomorphisms, the Yoneda embedding is
                     surjective, and G(x , x') ≃ (y x ＝ y x').

  EtaleGroupoids     (H6) Theorem 5.4.9: crisp étale groupoids are
                     microlinear, for the Rezk completion constructed in
                     RezkCompletion.

  CoverFiniteness    (H7) Astra's finiteness argument for abstract charts
                     (roadmap Section 3.6): Penon open subtypes (Myers's
                     Definition 6.2.6); a set covered by finitely many
                     Penon-open subtypes with at most one element each
                     is properly finite; so are the hom-sets of a
                     pregroupoid with a set of objects, given charts on
                     which the source map is injective, Penon open, and
                     finitely many of which contain each fibre of the
                     anchor; under univalence, so are the identity types
                     of the Rezk completion.

  SmoothLine         (H8) The smooth line: a commutative ring, Myers's
                     Postulate K, polynomial expressions, Weil algebras
                     by presentation (Definition 4.1.1 through Lemma
                     4.1.3) and their spectra (Remark 4.1.6); under K,
                     the points of a spectrum are infinitesimal and its
                     maps to 𝟚 are constant. Normalization: appending
                     the powers x_i^(k+1) gives a presentation with the
                     same spectrum, pointed and over Rⁿ, in which the
                     powers are among the equations. SmoothLine itself
                     constructs no quotient algebra; the comparison
                     with Weil algebras and their Hom-spectra is in
                     the Weil modules (WG1 to WG7, below).

  Microlinearity     (H8) Infinitesimal R-pushouts (Definitions 4.2.10
                     and 4.2.11), microlinear types (Definition 4.2.12)
                     and orbifolds (Definition 1.1.2), for spectra of
                     presentations (the literal forms, and the proof
                     that they agree, are in MyersMicrolinearity); T3
                     and T4 (Proposition 6.4.2, Corollary 6.4.4). For ℑ
                     the nullification at the crisp spectra (not shown
                     equivalent to Myers's infinitesimal-disk modality):
                     the test types are ℑ-connected, and under K types
                     with decidable equality are ℑ-modal.

  GlobalQuotients    (H8) T2, Theorem 6.4.1: for a crisp pointed
                     connected type with finite loop space and a family
                     over it whose fibre is a microlinear set, the
                     total space is an orbifold (ℑ as above, core item
                     4, Postulate K).

  FiniteGroupQuotients
                     (H8) Theorem 6.4.1 for a crisp finite group given
                     by a multiplication, through its torsors, under
                     univalence; also for the literal definitions.

  SquareEquivalences (H8, bridges) Being local is a proposition, and is
                     invariant under an equivalence of test squares
                     whose fourth vertex is a set.

  CrispTruncation    (H8, bridges) A crisp mere element of a crisp type
                     may be opened into any proposition, with the
                     native ♯ and no axiom (adapted from Fable's scratch
                     check of 13 November 2026). Since the
                     consolidation, typed aliases of the same lemmas in
                     gist.CohesiveApartness.SharpProperties and
                     gist.CohesiveApartness.CrispTruncation.

  MyersMicrolinearity
                     (H8, bridges) Myers's Definitions 4.2.1, 4.2.11,
                     4.2.12 and 1.1.2 in the adopted reading:
                     infinitesimal varieties as pointed types merely
                     equivalent to the spectrum of a Weil presentation,
                     crisp literal squares with crisp R-pushout proofs.
                     Microlinearity, orbifolds and nullification agree
                     with the formal ones (a comparison of code-defined
                     predicates); T2, T3 and T4 for the literal
                     definitions.

  SmoothOrder        (H9) Myers's Postulate O as printed, Postulate Exp
                     with its ordered-group structures, and the
                     translation law exported from Exp; basic order
                     lemmas under O and the translation law.

  Topology           (H9) Ordinary topologies (opens 𝓤-valued, unions
                     indexed by types in 𝓤, extensional openness);
                     locality of openness from a small basis;
                     Myers's Definition 5.1.1 and Lemmas 5.1.2, 5.1.3
                     and 6.2.7; subspace and product topologies;
                     continuity, homeomorphisms, open embeddings, local
                     homeomorphisms (the genuine predicate).

  LocalHomeomorphisms
                     (H9) A local homeomorphism restricted to an open
                     subset of a chart is a genuine open embedding;
                     every point lies in a basic open on which it is
                     one; a local homeomorphism injective on an open
                     subset is a genuine open embedding there.

  StableClassifier, LemmasAB, LemmasABForIm
                     (H9) The classifier of ¬¬-stable propositions,
                     and Lemmas A and B of the roadmap's Section 3.9 for
                     ℑ, with the universe convention of 13 November
                     (carriers in 𝓤 or 𝓤₀, one modality on 𝓤 ⁺);
                     adapted from Claude Fable 5.2's scratch checks,
                     with their proofs unchanged.

  SmoothOrderAlgebra (H9) Ring identities and ordered-field algebra
                     under O, the translation law and K: signs of
                     products, squares, inverses of positive elements,
                     a positive element below two given ones, intervals
                     and squares. No square roots.

  MetricTopology     (H9) Myers's Definition 5.1.4 and Theorem 5.1.5 in
                     every finite dimension: the metric topology of Rⁿ
                     is regular and T₀ (balls compared with boxes; T₀ by
                     K on the coordinate differences).

  Homeomorphisms     (H9) Final topologies; identity, composite, inverse
                     and restriction of homeomorphisms; invariance of
                     regularity, T₀ and local openness.

  Manifolds          (H9) Myers's Definition 5.1.6: ordinary manifolds of
                     fixed dimension, regular and T₀, with centred charts
                     that are genuine open embeddings and a countable
                     basis of chart domains as data; the laws over given
                     data (Ordinary-Manifold-Laws); local openness,
                     Hausdorffness, stability of opens.

  RationalPoints     (H9) The rational points (k − l)/(m + 1) of R, a
                     surjective enumeration, and their density, by
                     comparisons on a finite grid (Archimedes and
                     cotransitivity).

  SmoothLineManifold (H9, part of T5a) R is an ordinary 1-manifold: the
                     metric topology transported from R¹, translation
                     charts, the basis of rational intervals.

  ManifoldMicrolinearity
                     (H9) R, Rⁿ and metric opens are microlinear;
                     Myers's Lemmas 5.3.4 (sums over a modal index) and
                     5.3.3 (sums of étale maps); ordinary manifolds are
                     microlinear, by the sum of the basic opens.

  LemmaD             (H9) Fable's Lemma D: étaleness is local on the
                     source, along surjective étale maps.

  CoverProperness    (H9) The official cover-properness (crisp index type
                     and family, ordinary proofs, all ordinary points,
                     finite control of whole preimages) and its
                     consequence for fibres; the same condition for
                     covers indexed by sets, the memo's (added in the
                     third part of the consolidation), which the older
                     one implies.

  EtaleSourceMaps    (H9) The chart index "s is injective on B n",
                     ♭-discrete by Axiom C1 (since the consolidation,
                     by the consequence of C1 for decidable equality
                     in gist.RealCohesion.PunctualCohesion); covering,
                     injectivity and Penon openness of the charts; the
                     bridge 3.9: an ordinary local homeomorphism is
                     ℑ-étale.

  OrdinaryEtaleGroupoids
                     (H9) T1: for a crisp pregroupoid with ordinary
                     manifolds of objects and arrows, an ordinary local
                     homeomorphism as source map and a cover-proper
                     anchor, the Rezk completion is an orbifold; the
                     helper T1′; the literal form; the crisp-topology
                     specialization; and all four for set-indexed
                     covers, of which the literal one corresponds to
                     the memo's theorem (third part of the
                     consolidation).

  DubucPenon         (H10) Myers's Definition 6.2.1: Dubuc–Penon compact
                     types and proper maps, carriers and tests at one
                     universe; images, singletons, compact fibres of
                     proper maps (one direction of Proposition 6.2.4),
                     compact propositions are decidable.

  DualNumbers        (H10, consolidation) The dual numbers R[ε]/(ε²),
                     the injectivity half of Postulate J for them, and
                     the contradiction that their nilsquares cannot all
                     vanish, which T5a and T5b both use; from the smooth
                     line alone, without --cohesion.

  SmoothLineGroupoid (H10) T5a: the order defined by the ring and its
                     agreement with O (exp and log, once); the crisp
                     basis of division-free rational intervals; the unit
                     pregroupoid of R satisfies the hypotheses of T1
                     (crisp arrow basis, manifold laws, local
                     homeomorphism, cover-proper anchor, also for
                     set-indexed covers), and its anchor is not
                     Dubuc–Penon proper, by K and the injectivity half
                     of Postulate J for the dual numbers.

  CoveringProperty   (H10) Myers's Postulate E (the Covering Property) for
                     𝓤-valued subsets; Theorems 6.2.8 and 6.2.13, the
                     latter with 1/(n + 1).

  FiniteSubcovers    (H10) The composite of Myers's Remark 6.2.16, for
                     crisp subsets and crisp covers under the module's
                     hypotheses (Postulates O, Exp, K and E, and crisp
                     excluded middle), in finite-indexed-list form: for
                     a crisp Dubuc–Penon compact subset of a regular
                     space with a crisp countably indexed basis
                     B : ℕ → Subset X 𝓤, every crisp cover merely has a
                     finite list of indices, repetitions of indices or
                     opens allowed, whose members cover it (not a chosen
                     list, and not a finite set of opens). The proof
                     uses the argument of Corollary 6.2.14, then the
                     crisp refinement predicate, crisp excluded middle
                     and finite witness selection. Neither Corollary
                     6.2.14 nor Proposition 6.2.15 is stated
                     separately.

  C1Discreteness     (H10) Under Axiom C1: crisp propositions are
                     ♭-discrete, with crisp witnesses; crisp types with
                     decidable equality are ♭-discrete. Since the
                     consolidation, typed aliases of the statements of
                     gist.RealCohesion.PunctualCohesion.

  OrbitSets          (H10) Under Dubuc–Penon properness the orbit relation
                     is decidable; the crisp decision family (C1), the
                     small orbit set, effectiveness and decidable
                     equality; orbits, objects and arrows are ℑ-modal
                     (Corollary F′ at crisp representatives).

  ZeroDimensionalCharts
                     (H10) An ℑ-modal ordinary manifold has open
                     singletons and decidable equality at every point
                     (K and J for the dual numbers).

  ProperEtaleGroupoids
                     (H10) T5b: Dubuc–Penon properness of the anchor gives
                     open singletons and decidable equality on objects
                     and arrows, the genuine local homeomorphism, and
                     the official cover-properness; also for the literal
                     nullification, and both also for set-indexed
                     covers (third part of the consolidation).

  CrispCoverFiniteness
                     (H7) The index type of the charts: under crisp
                     excluded middle, crisp subtypes of ℕ are decidable
                     (the library's decide-at); subtypes of ℕ have
                     decidable equality. T1 over the abstract interfaces
                     (an intermediate result): the Rezk completion of a
                     crisp pregroupoid with étale source map, microlinear
                     objects and properly finite hom-sets is an orbifold.

  The comparison of Weil algebras with presentations (Weil gates WG1 to
  WG7 of Fable's plan [7], as released by Astra [8]). The ten modules
  of the algebraic core are --safe --without-K; WeilMicrolinearity is
  the crisp bridge, with --cohesion. Each header lists its
  declarations.

  Algebras           (WG1) Commutative algebras over the ring, with
                     carriers in any universe: homomorphisms, the
                     Hom-spectrum Specᴿ (all algebra homomorphisms to
                     R), the spectra of isomorphic algebras by
                     precomposition, and values of polynomial
                     expressions.

  PresentedAlgebras  (WG2) The interface Presented-Algebras: an algebra
                     R⟨ g ⟩ presented by a finite family g of
                     equations, with its relations, its universal
                     property for algebras in every universe, and
                     generation; homomorphisms from it are determined
                     by the generators, and any two instances give
                     isomorphic algebras.

  PresentedAlgebrasFromQuotients
                     (WG2) The construction: the quotient of polynomial
                     expressions by the congruence that the laws of a
                     commutative ring, the laws of the constants
                     (con-⊕ and con-⊗: con r ⊕ con s and con r ⊗ con s
                     are related to con (r + s) and con (r · s)) and
                     the equations g j ≈ 0 generate, from set quotients
                     given as a parameter, satisfies the interface.

  PresentedAlgebrasFromLargeQuotients
                     (WG2) The instance from TypeTopology's large set
                     quotients, with carriers in 𝓤₁, from fe, pt and
                     propositional extensionality for all universes.

  PresentedAlgebrasProperties
                     (WG3) For any instance: the Hom-spectrum of R⟨ g ⟩
                     is the type of solutions Sol g (Remark 4.1.6),
                     over Rⁿ, and pointed when the equations vanish at
                     the origin; translation and centering (the core of
                     Lemma 4.1.3); adjoining vanishing powers.

  NilpotentIdeals    (WG4) Finite sums and products in an algebra, the
                     ideal generated by a family, and the monomial
                     bound: if n generators have vanishing (k + 1)-st
                     powers, every product of k * n + 1 elements of
                     their ideal, possibly different, is zero.

  WeilAlgebras       (WG4) Myers's Definition 4.1.1, with the product
                     criterion for nilpotence: the algebra of
                     normalize P is a Weil algebra, every product of
                     succ (k * n) kernel elements being zero, and its
                     Hom-spectrum is Spec P as a pointed type.

  WeilAlgebraPresentations
                     (WG5) Lemma 4.1.3, from a finite presentation and
                     an augmentation; every Weil algebra, in any
                     universe, is merely the algebra of a Weil
                     presentation, as an augmented algebra, and its
                     Hom-spectrum merely Spec P, as a pointed type.

  WeilVarieties      (WG6) Myers's Definition 4.2.1 for Weil algebras,
                     compared with the presented varieties: both
                     directions for algebras in the universe of the
                     instance, the reverse one in any universe.

  WeilVarietiesFromLargeQuotients
                     (WG6) The closed endpoints at the constructed
                     instance, in 𝓤₁: presented-algebra, remark-4-1-6,
                     lemma-4-1-3, is-Weil-variety and the comparisons of
                     spectra and of varieties; no quotient, instance or
                     universe parameter.

  WeilMicrolinearity (WG7) The crisp bridge: the Weil-variety predicate
                     agrees with the library's; whole crisp pointed
                     test squares of Weil varieties, each crisp
                     together with its R-pushout proof (squares of
                     pointed types, not of algebra maps), give the same
                     microlinear types and orbifolds; on a given
                     subuniverse, nullification at the old generators
                     is nullification at the whole crisp Weil-variety
                     packages. Separately, for nullity tests only:
                     nullity at the old generators gives nullity at the
                     spectrum of every crisp Weil algebra, in any crisp
                     universe of carriers, and conversely for carriers
                     in 𝓤₁, with algebra, augmentation and Weil proof
                     crisp and the explicit Lift maps. No reflector,
                     and no nullification at families of algebras, is
                     constructed.

Assumptions. Univalence is a module parameter of Deloopings,
RezkCompletion and CoverFiniteness (in each, of a nested module only),
and of GroupQuotients, EtaleGroupoids, the second part of
CrispCoverFiniteness, FiniteGroupQuotients, OrdinaryEtaleGroupoids
(univalence of the universe of the carriers, for T1) and
SmoothLineGroupoid (univalence of 𝓤₀, for theorem-T5a); nothing else
assumes it. The smooth line is a module parameter (a commutative ring) of
Microlinearity, GlobalQuotients, FiniteGroupQuotients and
MyersMicrolinearity; Postulate K and the hypotheses on ℑ are
hypotheses of the statements that use them. For T2 for groups given by
a multiplication, univalence of the universe of the group is an
ordinary module parameter (FiniteGroupQuotients). The crisp elimination
of truncations uses the native ♯ of Agda 2.9.0, with no axiom. Crisp
excluded middle is a hypothesis of crisp-subtypes-of-ℕ-are-decidable,
and so of the finite subcovers of T5b (FiniteSubcovers,
ProperEtaleGroupoids); it is not used by T1 or T5a. For gate H9, Postulate O,
Postulate Exp (for the translation law) and Postulate K are hypotheses of the
topological and manifold modules; Axiom C1, for an arbitrary family of pointed
generators, is a hypothesis of T1 (the ♭-discreteness of the chart index);
propositional extensionality at 𝓤, from univalence for T1, is a hypothesis of
Lemma B. For T5a, Postulate J for the fixed crisp algebra of dual numbers, in
its injectivity half, is a hypothesis of the non-properness of the anchor, and
exp and log are used once, for square roots of positive elements. For T5b,
Postulate E (the Covering Property) at the universe of the carriers, J for the
dual numbers, Axiom C1 and crisp excluded middle are hypotheses of the
statements that use them (CoveringProperty, FiniteSubcovers, C1Discreteness,
OrbitSets, ZeroDimensionalCharts, ProperEtaleGroupoids).
For the Weil comparison, propositional extensionality for all
universes, Prop-Ext, is an explicit parameter of three modules: an
ordinary one of PresentedAlgebrasFromLargeQuotients and
WeilVarietiesFromLargeQuotients, and a crisp one of
WeilMicrolinearity, with crisp function extensionality, propositional
truncations, ring and universe of the tests. No existing hypothesis
supplies it: the univalence hypotheses above are ordinary and of one
universe, which gives propositional extensionality of that universe
only. The Weil modules bring the first imports of TypeTopology's
Quotient.Type (PresentedAlgebrasFromQuotients) and Quotient.Large
(PresentedAlgebrasFromLargeQuotients) into this folder; none of them
imports Quotient.Effectivity, Fin.Choice, Fin.Pigeonhole or
UF.Univalence directly, or assumes small quotients, resizing, choice,
univalence, excluded middle, Axiom C1 or Postulate K. The existing
statements keep their own hypotheses.

Flags. --safe --without-K wherever possible; --cohesion only where a
crisp variable or ♭ occurs, or where a module imports one that has
it (--cohesion is infective: this index has it because it imports
Nullification). Every assumption is a module parameter;
there are no postulates, holes or termination pragmas. Nullification
(the modality ℑ) is a module parameter; deloopings and the Rezk
completion are constructed, under univalence [2, Section 4].

AI disclosure. The Agda code and the prose in this folder are by
Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger in a conversation of 12 and 13 November 2026. The plan, the order
of the gates and the formal readings of the targets are from the
roadmap [2] by Claude Fable 5.2, an AI model made by Anthropic. The
paper proofs that the formalization follows are by GPT-6 Astra [3],
except Lemmas A–D, F and G, which are Fable's and were audited by
Astra; each module names the note it follows. The modality layer
(Modalities, Nullification) proves standard facts about modalities,
from Rijke, Shulman and Spitters and from Cherubini and Rijke, which
the roadmap lists without proof; the proofs are Claude Opus 5.5's,
and its modules name these sources. The modules StableClassifier,
LemmasAB and LemmasABForIm, and the proofs of CrispTruncation, are
adapted from scratch checks by Claude Fable 5.2 for this project; their
headers give the source files and hashes. Nothing here is
transcribed from agda-unimath yet; a module that transcribes from it
will say so, with the commit, and a copy of its licence will be kept
beside it. The final repairs of 13 November 2026, after the final
audits by Claude Fable 5.2 and GPT-6 Astra, are by Claude Opus 5.5 in
the same conversation, following Fable's repair plan as reviewed by
Astra: prose made precise, the type of theorem-T5b-literal displayed,
the imports sorted, and the code reformatted to lines of at most 80
characters; apart from that type and the order of the imports, the
code changed in whitespace only. The consolidation of 13 November 2026
is also by Claude Opus 5.5 in the same conversation, following steps K1
and K3 of Fable's consolidation plan as released by Astra: the dual
numbers and the nilsquare contradiction moved unchanged to DualNumbers,
which SmoothLineGroupoid and ZeroDimensionalCharts name by typed
aliases, so that ZeroDimensionalCharts no longer imports
SmoothLineGroupoid; the lemmas of CrispTruncation moved unchanged to
gist/CohesiveApartness, and CrispTruncation names them by typed
aliases. No existing name was removed, and no existing statement
changed. In the second part of the consolidation, on the same day and
by Claude Opus 5.5 in the same conversation (steps K4 and K5 of the
plan, as corrected by its addendum 01 and released by Astra), the
statements of C1Discreteness became typed aliases of those of
gist.RealCohesion.PunctualCohesion, with their types and module
parameters, the Boolean test of Nullification became that of
gist.RealCohesion.BooleanTests, with Nullification keeping its
ordinary function extensionality, and the proof that the chart index
of EtaleSourceMaps is ♭-discrete became the consequence of Axiom C1
for decidable equality, with its type; again no existing name was
removed, and no existing statement changed.
In the third part of the consolidation, on the same day and by Claude
Opus 5.5 in the same conversation (Claude Fable 5.2's plan for the
memo's set-indexed cover-properness, as reviewed and released by Astra
[5]), CoverProperness gained the condition for set-indexed covers, with
its restriction from the older condition, and OrdinaryEtaleGroupoids,
SmoothLineGroupoid and ProperEtaleGroupoids gained the forms of T1, T5a
and T5b for it; the proof of T1 is now stated once, and theorem-T1′ and
theorem-T1 apply it after the restriction. The scope of the statements
was made precise in the module headers and above. No existing name was
removed, no existing statement changed, and no import edge between the
library modules changed; the only new imports are TypeTopology's
UF.Sets, in CoverProperness, and UF.DiscreteAndSeparated, in
OrdinaryEtaleGroupoids.
In the packaging release of the same day [6], by Claude Opus 5.5 in
the same conversation, every bibliography entry for a local note
gained the path of its file in references/, the paragraph on the scope
of the statements was read against the printed paper, and the
qualifications of the plan of [6] were applied in the module headers;
no code changed.
The eleven modules of the Weil comparison are by Claude Opus 5.5 in the
same conversation, one Weil gate at a time, following Claude Fable
5.2's plan as reviewed by GPT-6 Astra and amended by Fable's addendum
01, as released and accepted gate by gate by Astra, with Fable's audit
of each gate [7, 8]. The exported names and the shapes of the
statements are Fable's; the two direct-algebra proofs of
WeilMicrolinearity are the drafts of the addendum, Section 2, token for
token, and several of its definitions and proofs are those of
MyersMicrolinearity after renaming; the provenance ledger of the
package records these and the other origins. Their integration here
(WG8) added the eleven import lines below and changed prose only.

The bibliographies retain titles and identifiers of the project notes
used in writing the proofs. The public sources and the dependencies of
the main theorem are listed in orbifolds/README.md of the cohesion
repository.

[1] D. J. Myers. Orbifolds as microlinear types in synthetic
    differential cohesive homotopy type theory. arXiv:2205.15887v1.
    https://arxiv.org/abs/2205.15887v1
[2] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026 (with the amendment of the same day).
    references/F01-orbifolds-roadmap-rev2.md
[3] GPT-6 Astra. Notes on the adopted core and on Myers's paper,
    11 and 12 November 2026 (the folder proof/ of [2]).
    references/A01-section-6-4-over-the-core.txt
    references/A02-dp-properness-implies-replacement.txt
    references/A03-cover-finiteness.txt
    references/A04-cover-properness-stability.txt
    references/A05-lemmas-F-G-audit.txt
    references/A06-adopted-core.txt
    references/A07-main-aims-scope.txt
    references/A08-section-2-4-point-presentations.txt
    references/A09-roadmap-scope-audit.txt
    references/A10-open-charts-etale.txt
[4] M. Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer Science
    28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3
[5] GPT-6 Astra. Consolidation implementation, third release
    (OPUS-CONSOLIDATION-RELEASE-03), 13 November 2026, with
    COVER-INDEX-PLAN-REVIEW and Claude Fable 5.2's plan
    (references/F20-cover-index-plan.md, SHA-256
    10fb9683…), and the memo on Myers's foundations and properness.
    references/A33-consolidation-release-03.txt
    references/A34-cover-index-plan-review.txt
    references/C11-myers-memo-2026-11-13.tex
[6] GPT-6 Astra. Portable local packaging, release 04
    (OPUS-CONSOLIDATION-RELEASE-04), 13 November 2026, with Claude
    Fable 5.2's plan for packaging and provenance of the same day,
    Sections 3 and 5.
    references/A37-consolidation-release-04.txt
    references/F21-packaging-plan.md
[7] Claude Fable 5.2. Plan: formalizing the comparison of Weil algebras
    with presentations, 13 November 2026, with its statement companion
    and its addendum 01; GPT-6 Astra's review of the plan.
    references/F22-weil-plan.md
    references/F22a-weil-plan-statements.txt
    references/F23-weil-plan-addendum-01.md
    references/A40-weil-plan-review-01.txt
[8] GPT-6 Astra. Releases of the Weil gates WG1 to WG8, 13 November
    2026 (local time), and the documentation corrections that WG8
    carries.
    references/A42-weil-release-wg1.txt
    references/A43-weil-release-wg2.txt
    references/A44-weil-release-wg3.txt
    references/A45-weil-release-wg4.txt
    references/A46-weil-release-wg5.txt
    references/A47-weil-release-wg6.txt
    references/A48-weil-release-wg7.txt
    references/A49-weil-release-wg8.txt
    references/A61-wg8-required-packaging-corrections.txt

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

module gist.Orbifolds.index where

import gist.Orbifolds.AbstractOrbifolds
import gist.Orbifolds.Algebras
import gist.Orbifolds.C1Discreteness
import gist.Orbifolds.CoverFiniteness
import gist.Orbifolds.CoveringProperty
import gist.Orbifolds.CoverProperness
import gist.Orbifolds.CrispCoverFiniteness
import gist.Orbifolds.CrispLemmaF
import gist.Orbifolds.CrispTruncation
import gist.Orbifolds.Deloopings
import gist.Orbifolds.DualNumbers
import gist.Orbifolds.DubucPenon
import gist.Orbifolds.EtaleGroupoids
import gist.Orbifolds.EtaleQuotients
import gist.Orbifolds.EtaleSourceMaps
import gist.Orbifolds.FiniteGroupQuotients
import gist.Orbifolds.FiniteSubcovers
import gist.Orbifolds.GlobalQuotients
import gist.Orbifolds.GroupQuotients
import gist.Orbifolds.Homeomorphisms
import gist.Orbifolds.LemmaD
import gist.Orbifolds.LemmaF
import gist.Orbifolds.LemmaG
import gist.Orbifolds.LemmasAB
import gist.Orbifolds.LemmasABForIm
import gist.Orbifolds.LocalHomeomorphisms
import gist.Orbifolds.ManifoldMicrolinearity
import gist.Orbifolds.Manifolds
import gist.Orbifolds.MetricTopology
import gist.Orbifolds.Microlinearity
import gist.Orbifolds.Modalities
import gist.Orbifolds.MyersMicrolinearity
import gist.Orbifolds.NilpotentIdeals
import gist.Orbifolds.Nullification
import gist.Orbifolds.OrbitSets
import gist.Orbifolds.OrdinaryEtaleGroupoids
import gist.Orbifolds.PresentedAlgebras
import gist.Orbifolds.PresentedAlgebrasFromLargeQuotients
import gist.Orbifolds.PresentedAlgebrasFromQuotients
import gist.Orbifolds.PresentedAlgebrasProperties
import gist.Orbifolds.ProperEtaleGroupoids
import gist.Orbifolds.ProperFiniteness
import gist.Orbifolds.RationalPoints
import gist.Orbifolds.RezkCompletion
import gist.Orbifolds.SmoothLine
import gist.Orbifolds.SmoothLineGroupoid
import gist.Orbifolds.SmoothLineManifold
import gist.Orbifolds.SmoothOrder
import gist.Orbifolds.SmoothOrderAlgebra
import gist.Orbifolds.SquareEquivalences
import gist.Orbifolds.StableClassifier
import gist.Orbifolds.TestSquares
import gist.Orbifolds.Topology
import gist.Orbifolds.WeilAlgebraPresentations
import gist.Orbifolds.WeilAlgebras
import gist.Orbifolds.WeilMicrolinearity
import gist.Orbifolds.WeilVarieties
import gist.Orbifolds.WeilVarietiesFromLargeQuotients
import gist.Orbifolds.ZeroDimensionalCharts

\end{code}
