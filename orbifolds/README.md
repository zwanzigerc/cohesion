# Orbifolds as microlinear types

David Jaz Myers defines an orbifold to be a microlinear type in which the type of identifications between any two points is properly finite. We retain his Definition 1.1.2. We change the hypotheses of Theorem 6.3.7 so that the theorem includes the unit groupoid of the smooth line, already an example of an ordinary proper étale Lie groupoid. Section and theorem numbers here refer to the first arXiv version of Myers’s paper. [Myers, *Orbifolds as microlinear types in synthetic differential cohesive homotopy type theory*](https://arxiv.org/pdf/2205.15887v1)

## The revised main theorem

**Theorem.** Let $G$ be a crisp pregroupoid. Suppose its object and arrow types are ordinary finite-dimensional manifolds, the source $s:G_1\to G_0$ is an ordinary local homeomorphism, and the anchor $(s,t):G_1\to G_0\times G_0$ is cover-proper. Supply a crisp countable basis for the arrow manifold. Then the Rezk completion of $G$ is an orbifold. In particular, its identity types have decidable equality and are merely quotients of subtypes of finite sets. `Orbifolds.OrdinaryEtaleGroupoids` · `Orbifolds.ProperFiniteness`

Here each manifold has a regular $T_0$ topology, centered charts from ordinary open subsets of Euclidean space over the smooth line $R$, and a countable basis of chart domains. Its topology, dimension, chart-existence proofs and manifold laws may all be ordinary. An object basis may also be ordinary. The paper argument takes crisp bases on both manifolds. The Agda declaration with the weaker object-basis hypothesis is `theorem-T1-literal-for-set-indices`. `Orbifolds.Manifolds` · `Orbifolds.LocalHomeomorphisms`

A map $p:E\to B$ is **cover-proper** if, for each crisp family of ordinary opens covering $E$, indexed by a crisp $\flat$-discrete set, and for each ordinary point $b:B$, there merely exist an open neighborhood $W$ of $b$ and a finite list of indices whose opens cover $p^{-1}(W)$. The opens must cover every ordinary point of $E$. They may overlap. In the proof we apply this condition to source charts on which $s$ is injective. The finite list bounds each hom-set, and the charts supply the equality decisions needed for proper finiteness. Ordinary charts also give formal étaleness of $s$. Étale descent then carries microlinearity from the object manifold to its Rezk completion. `Orbifolds.CoverProperness` · `Orbifolds.EtaleSourceMaps` · `Orbifolds.CrispLemmaF`

The change of properness is strict. The anchor of the unit groupoid of $R$ is the diagonal. Its fibre over $(x,y)$ is the proposition $x=y$, so a Dubuc–Penon proper diagonal would give decidable equality on $R$, contradicting K and J for the dual numbers. The diagonal is cover-proper. Conversely, under the stronger hypotheses of `theorem-T5b-literal-for-set-indices`, a manifold pregroupoid with a formally étale source and a Dubuc–Penon proper anchor has open singletons and decidable equality on objects and arrows, an ordinarily locally homeomorphic source, and a cover-proper anchor. `Orbifolds.SmoothLineGroupoid` · `Orbifolds.ProperEtaleGroupoids`

## Axioms of the revised foundation

We use crisp homotopy type theory with abstract cohesion. The smooth line $R$ below is a supplied commutative ring. Its axioms are separate from those of the Dedekind reals used in the Shulman development.

1. **Crisp excluded middle.** Every crisp proposition is decidable in the crisp context.
2. **Shulman’s C1, including C0.** C0 supplies abstract shape and its adjunction. C1 gives a family of pointed generators detecting discrete types. [Shulman, §§8 and 10](https://arxiv.org/pdf/1509.07584v3)
3. **Shape of the smooth line.** The abstract shape of $R$ is contractible.
4. **Infinitesimal shape.** $ℑ$ is nullification at all crisp finite infinitesimal Weil varieties, and preserves crisp pullbacks. This is the alternative in Myers’s Remark 4.3.2. `Orbifolds.Nullification` · `Orbifolds.MyersMicrolinearity`
5. **Axioms for the smooth line.** K says $0\ne1$ and a finite tuple whose coordinates are not all zero has an invertible coordinate. O specifies an Archimedean, irreflexive, cotransitive strict order, with positive sums and products and a sign for every nonzero element. Exp identifies the additive group with the multiplicative group of positive elements as ordered groups. E says that if two subsets cover $R$, every point has a ball of positive radius contained in one of them. Constancy says that a map $R\to R$ invariant under every square-zero displacement is constant. J says evaluation $W\to (\operatorname{Spec}_R W\to R)$ is an isomorphism for each fixed crisp finite Weil algebra $W$, allowing ordinary maps and coefficients. W asserts the tininess of crisp finite Weil varieties in the crisp-adjunction sense. [Myers, Axiom 3 and §4](https://arxiv.org/pdf/2205.15887v1#page=30) · `Orbifolds.SmoothLine` · `Orbifolds.SmoothOrder` · `Orbifolds.CoveringProperty`

## Axioms used by the main theorem

| Assumption | Use in the Agda proof |
| --- | --- |
| Reflective all-Weil nullification, preserving crisp pullbacks | Infinitesimal stability of ordinary opens, manifold microlinearity, formal étaleness of the source, and étale descent. The reflector and its laws are supplied. |
| K and O | Infinitesimal stability and the topology of the ordinary Euclidean charts. |
| Exp, for translation invariance of the strict order | The manifold interface takes this law for the same order as O. The proof uses just the additive ordered-group field of Exp. |
| C1 for a family of pointed generators | The set of indices of the injective source charts is $\flat$-discrete. |
| Crisp function extensionality, propositional truncations and the smooth ring, together with univalence in the object-and-arrow universe | These are explicit ambient inputs. Univalence supplies propositional extensionality at that universe and enters the construction of the Rezk completion. |

The paper proof uses all-Weil nullification, preservation of crisp pullbacks, K and O, with extensionality, truncations, modal elimination and Rezk completion understood. It uses crisp excluded middle to obtain an admissible chart index from a crisp basis. Supplying the admissible atlas removes that use. Agda takes C1 to prove the index is $\flat$-discrete, assumes the translation law through Exp, and dispenses with crisp excluded middle. Contractible shape of $R$, J, W, E and Constancy play no part in the main theorem. `Orbifolds.OrdinaryEtaleGroupoids`

## Other checked results and changes of scope

Theorems 5.4.1 and 5.4.9 follow by étale descent without tiny types. Section 6.4 gives finite-group quotients of microlinear sets, pullbacks of orbifolds and the inertia orbifold. The corrected form of Lemma 6.3.4 proves that every smooth-real curve in an all-Weil-modal subtype of a crisp ordinary manifold is constant. The main theorem obtains decidable equality from source charts. `Orbifolds.EtaleQuotients` · `Orbifolds.MyersMicrolinearity`

The corrections table lists the changes to both Myers papers, including every identified use of Shulman’s Lemma 8.15, the point descriptions of §2.4, and the hypotheses under which cover-proper maps are stable under base change. Each entry identifies the scope of the proof. [Complete corrections and resolutions](corrections.md)

## Sources and code

The Agda code imports Martín Escardó and contributors’ TypeTopology at commit `52ed2eb58d72a6bab0dd70480fa73e2291b08219`. It uses the library’s finite types, groups, torsors, reflective subuniverses, univalent foundations and set quotients. In particular, the construction of presented algebras uses `Quotient.Type` and `Quotient.Large`. TypeTopology’s GPLv3 grants permission for reuse and redistribution under its terms. [TypeTopology source](https://github.com/martinescardo/TypeTopology/tree/52ed2eb58d72a6bab0dd70480fa73e2291b08219/source) · [TypeTopology license](../apartness/notices/TypeTopology-LICENSE.txt)

The provenance notes record agda-unimath as a reference consulted for subfinite sets and DCHoTT-Agda as a planning reference. They record no code copied from either library into the Orbifolds modules. The shared cohesion modules have their own sources and notices. The group construction in TypeTopology’s `Groups.Free` served as a design precedent for the universal property of presented algebras. [agda-unimath](https://github.com/UniMath/agda-unimath/tree/75518656f287c203b41cb7f71df46e02b987a084) · [DCHoTT-Agda](https://github.com/felixwellen/DCHoTT-Agda/tree/ca8c755af0b26f8f50c5a60d3b7f9384a26f5d0e) · [TypeTopology’s free-group construction](https://github.com/martinescardo/TypeTopology/blob/52ed2eb58d72a6bab0dd70480fa73e2291b08219/source/Groups/Free.lagda)

Colin Zwanziger directed the project. Claude Fable 5.2 and GPT-6 Astra developed and reviewed the arguments, and Claude Opus 5.5 implemented the modules. Fable found the two inconsistencies in Myers’s printed axiom package. Some code was also reused within this project. The set-indexed cover predicate incorporates Fable’s Agda construction. Two proof terms comparing nullity at Weil spectra come directly from Fable’s draft, and several definitions and proofs in `WeilMicrolinearity` reuse `MyersMicrolinearity` with renamed identifiers and an adjustment of universe level. `Orbifolds.CoverProperness` · `Orbifolds.WeilMicrolinearity`

## Checking

Agda 2.9.0 checked the complete `gist.Orbifolds.index` locally at the TypeTopology revision cited above. The index imports all 59 other Orbifolds modules. They use Agda’s safe mode, with axioms supplied as explicit hypotheses.
