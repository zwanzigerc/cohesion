# Real cohesion, the intermediate value theorem, and Brouwer's fixed-point theorem

The approximate intermediate value theorem holds for **every** function on the Dedekind reals. The two classical Brouwer theorems hold for the closed unit ball in every finite dimension. Both need fewer axioms than Shulman used for the disc. We use the numbering of Michael Shulman's *Brouwer's fixed-point theorem in real-cohesive homotopy type theory*. [Shulman, arXiv v3](https://arxiv.org/abs/1509.07584v3)

## The approximate intermediate value theorem

Let $f\colon\mathbb R\to\mathbb R$ and let $p,q,a,b$ be reals. If $p<q$, $f(a)<q$, and $p<f(b)$, then there exists a **rational** $r$ such that $p<f(r)<q$. The function, the bounds, and the points may all vary in an ordinary cohesive context. Taking $p=c-\varepsilon$ and $q=c+\varepsilon$ gives Shulman's Theorem 11.4 with the crispness assumptions removed from both $f$ and $c$. The witness is propositionally truncated. The statement asserts existence on the whole real line. [Agda theorem with rational witness](../typetopology/source/gist/RealCohesion/Theorems.lagda)

Real cohesion ($R♭$) suffices. No choice, excluded middle, univalence, or analytic Markov principle is required. The proof adapts Matthew Frank's interpolated bisection. Where Frank uses pointwise continuity, we use the fact that a function positive at the limit of a rapidly converging sequence must be positive at some term. A finite-chain argument in a discrete quotient gives this conclusion even for an ordinary function. [Frank's proof](https://lmcs.episciences.org/6636) · [Agda proof](../typetopology/source/gist/RealCohesion/ApproximateIVT.lagda)

## The two classical Brouwer fixed-point theorems

Let $B^n$ be the closed Euclidean unit ball, for any crisp natural number $n$. With crisp excluded middle, Shulman's Axiom C1 for a crisp family of pointed generators, and the hypothesis that the Dedekind reals are not ♭-discrete, we prove both of the following.

- **Sharp Brouwer, Theorem 12.4.** Every ordinary $f\colon B^n\to B^n$ sharply has a fixed point, in the sense $\sharp\lVert\sum_{x:B^n} f(x)=x\rVert$.
- **Crisp Brouwer, Corollary 12.5.** For every **crisp** $f\colon B^n\to B^n$, there exists $x:B^n$ such that $f(x)=x$. Here the conclusion is the ordinary propositional truncation $\lVert\sum_{x:B^n} f(x)=x\rVert$.

Shulman's assumptions for the disc were univalence, crisp excluded middle, $R♭$, and Axiom T. Real cohesion implies C1 and the required failure of ♭-discreteness of $\mathbb R$. Our proof dispenses with both T and univalence. It proves Kuhn's cubical lemma in every dimension, obtains the fixed-point theorems for the cube, and uses the ball as a retract of the cube. The Agda proof of Kuhn's lemma follows John Harrison's combinatorial argument via Robert Himmelmann's Isabelle/HOL translation. [Agda fixed-point theorems](../typetopology/source/gist/RealCohesion/Theorems.lagda) · [Kuhn's lemma in Agda](../typetopology/source/gist/RealCohesion/KuhnLemmaGeneral.lagda) · [Isabelle formulation of Kuhn's lemma](https://isabelle.in.tum.de/library/HOL/HOL-Analysis/Brouwer_Fixpoint.html)

A further version permits an ordinary family of C1 generators. Its extra assumption, written **NC** below, is that for some generator $G$, some $g:G\to\mathbb R$, and some $u,v:G$, we have $g(u)<g(v)$. Only the propositional truncation of this existence statement is used. The real line with its identity map gives such a generator under $R♭$. This weaker assumption also suffices for the approximate IVT. As throughout the Agda development, assertions about which cohesive axioms suffice are relative to the stated type-theoretic foundations, including function and propositional extensionality and propositional truncation. [Theorems from C1 and NC](../typetopology/source/gist/RealCohesion/TheoremsFromC1.lagda)

## The nLab open problems

We resolve six questions from the nLab’s *Open problems in homotopy type theory*. Shulman raised the questions about the shape of subsets of the reals, analytic Markov’s principle, and the approximate intermediate value theorem in his paper. Anonymouse posed the question about the full fan theorem and the two about tight apartness. We quote the nLab’s wording, using revision 33 for the apartness questions. [Shulman, §§8.3 and 11](https://arxiv.org/abs/1509.07584v3) · [nLab problem list](https://ncatlab.org/nlab/show/open+problems+in+homotopy+type+theory#InCohesiveHomotopyTypeTheory) · [nLab revision 33](https://ncatlab.org/nlab/revision/open+problems+in+homotopy+type+theory/33#InCohesiveHomotopyTypeTheory) · [nLab attribution and reuse policy](https://ncatlab.org/nlab/show/HomePage)

### 1. Shape of subsets of the reals

> Assuming the axiom of real cohesion, is the shape of every subset of the Dedekind real numbers a set?

**No.** In Shulman’s intended higher sheaf model, the image of a continuous real function has a shape whose fundamental group surjects onto $\mathbb Z$. This gives a counterexample to the conjecture he raises in §11 immediately after Theorem 11.3.

Agda also checks a conditional internal refutation. It constructs a specific crisp subset of the Dedekind reals, the image of a dyadic function, and proves that its shape is not a set using a mod-two obstruction. In addition to real cohesion and crisp excluded middle, the proof assumes unique Boolean real-path descent and that the type of two-element types is modal. The paper explains why these two principles hold in the intended model. [Agda construction and hypotheses](../typetopology/source/gist/RealCohesion/RealSubsetShape.lagda#L20) · [Checked theorem](../typetopology/source/gist/RealCohesion/Theorems.lagda#L313)

### 2. Analytic Markov's principle

> Assuming the axiom of real cohesion and crisp excluded middle, prove that the analytic Markov's principle is cohesively true.

**No.** A sheaf model with a pointless end satisfies real cohesion, crisp excluded middle and sharp choice, but refutes the implication $\neg(x\leq0)\Rightarrow 0<x$. Shulman conjectures the implication in §8.3 before Theorem 8.32 and asks for a countermodel to Axiom T after Example 8.34. Under crisp excluded middle the two principles are equivalent. They hold in his intended model, so the result is independence. Lean checks the counterexample in ordinary sheaves. The higher sheaf argument uses a Cartesian enlargement of the site and the interpretation discussed in Remark 7.5. [Lean results and source coverage](../lean/README.md#countermodels)

### 3. The full fan theorem

> Assuming the axiom of real cohesion and crisp excluded middle, does the full fan theorem hold cohesively? (i.e. is Cantor space a spatial locale?)

**No.** The same pointless-end model has a bar on the binary tree that meets every branch but has no uniform bound on any covering family. The full fan theorem holds in the intended model. Lean checks this bar in the ordinary sheaf model. Agda derives the obstruction from explicit hypotheses on a bar. Anonymouse added the question in nLab revision 33. [Lean results and source coverage](../lean/README.md#countermodels) · [nLab revision introducing the question](https://ncatlab.org/nlab/revision/diff/open+problems+in+homotopy+type+theory/33) · [Agda bar obstruction](../typetopology/source/gist/RealCohesion/BinaryBarObstruction.lagda)

### 4. The approximate intermediate value theorem

> Prove the approximate intermediate value theorem in Mike Shulman’s model of real-cohesive homotopy type theory without resorting to crispness.

**Yes.** Axiom $R♭$ suffices for an arbitrary function and an arbitrary target value, and the approximate witness can be rational. Shulman asks this immediately after Theorem 11.4. [Statement and proof](#the-approximate-intermediate-value-theorem)

### 5. Crisp representability of tight apartness

> Suppose a discrete cohesive type A comes with a tight apartness relation. Then, assuming crisp excluded middle and axiom C1, is the tight apartness relation on A a crisp relation?

**No.** Representability of every such relation is equivalent to excluded middle in the cohesive mode and fails in real cohesion. Shulman introduces the background axioms in §8, including C1 in §8.2. The question is Anonymouse’s. [nLab, revision 33](https://ncatlab.org/nlab/revision/open+problems+in+homotopy+type+theory/33#InCohesiveHomotopyTypeTheory) · [Apartness proof](../apartness/README.md)

### 6. Decidability of tight apartness on ♭A

> Suppose a cohesive type A comes with a tight apartness relation. Then, assuming crisp excluded middle and axiom C1, is the tight apartness relation on ♭A in the cohesive mode decidable?

**No.** Decidability of every such induced relation is again equivalent to excluded middle in the cohesive mode and fails in real cohesion. Anonymouse poses this companion question under the same hypotheses from Shulman §8. [nLab, revision 33](https://ncatlab.org/nlab/revision/open+problems+in+homotopy+type+theory/33#InCohesiveHomotopyTypeTheory) · [Apartness proof](../apartness/README.md)

## Questions raised by Shulman

Here LEM means **crisp** excluded middle, AC means Shulman's **sharp** axiom of choice, and T says that $0<x$ is a codiscrete proposition for every real $x$. The references in the first column locate where Shulman actually raises each question. [Shulman's paper](https://arxiv.org/abs/1509.07584v3)

| Place in Shulman | Question | Resolution |
| --- | --- | --- |
| §3.2, displayed formula (3.2) and the paragraph following it | Is there a concrete counterexample to this stronger choice principle? | **Yes.** In a real-cohesive higher sheaf model, the chart $B\mathbb R$ refutes (3.2) while sharp choice, LEM, $R♭$ and T hold. Lean checks that (3.2) fails at that chart and sharp choice (3.3) holds in the same $(2,1)$-category of stacks. The paper proves independence at the higher level using the interpretation in Remark 7.5 and verifies that (3.2) holds in Shulman’s intended model. [Lean results and source coverage](../lean/README.md#countermodels) |
| §8.3, before Theorem 8.32 and after Example 8.34 | Does analytic Markov follow from LEM and $R♭$? Is there a countermodel to T with both axioms? | **No** to the implication and **yes** to the countermodel, because the same model refutes both principles. [nLab problem 2](#2-analytic-markovs-principle) |
| §10, final paragraph discussing Lawvere's continuity | Do $R♭$ and AC imply that $\int(A^S)\to(\int A)^S$ is an equivalence for every crisp set $A$ and crisp discrete set $S$? | **No.** In a long-ray model the comparison already fails to be injective on components for a particular wedge $A$ and $S=\mathbb N$. Lean checks that two distinct elements have the same image under the ordinary comparison. The extension to full shape in higher sheaves on the same site is a paper proof. [Lean results and source coverage](../lean/README.md#countermodels) |
| §11, after Theorem 11.3 | Is the shape of every subset of $\mathbb R$ a set? | **No.** The image of an oscillating real function supplies a counterexample in the intended model. [nLab problem 1](#1-shape-of-subsets-of-the-reals) |
| §11, after Theorem 11.4 | Can one remove crispness from the approximate IVT? | **Yes.** The proof works under $R♭$ alone. [nLab problem 4](#4-the-approximate-intermediate-value-theorem) |
| §11, after Corollary 11.6 | Can one characterize the functions $\mathbb R^n\to\mathbb R$ on points for all finite dimensions, without further axioms? | **Yes.** For every crisp $n$, the canonical map from $\flat(\mathbb R^n\to\mathbb R)$ to functions $\flat(\mathbb R^n)\to\flat\mathbb R$ is injective and its image consists exactly of the $\varepsilon$–$\delta$ continuous functions. The full characterization uses LEM and $R♭$. [Agda statements](../typetopology/source/gist/RealCohesion/ShulmanWeakeningsStatements.lagda) |

Shulman also asks, after Theorem 12.6, whether the approximate Brouwer theorem for the disc can dispense with crispness of the function under his original axioms ($R♭$ and univalence). For arbitrary maps our positive theorem assumes LEM, $R♭$ and T, works in all finite dimensions, and dispenses with univalence. That answers the question **yes under these additional assumptions**. The release gives no resolution for arbitrary maps from the original axioms alone. [Agda fixed-point statements](../typetopology/source/gist/RealCohesion/BrouwerStatements.lagda)

## Weakened and corrected statements

The following table compares Shulman's printed hypotheses with the results of this development. The supplemental [table of 73 Agda statements](weaker-cohesion.md) links each theorem under $R♭$ to its version under C1 and mere NC. [Printed axioms and results](https://arxiv.org/abs/1509.07584v3) · [Agda theorems](../typetopology/source/gist/RealCohesion/Theorems.lagda) · [Agda theorems under C1](../typetopology/source/gist/RealCohesion/TheoremsFromC1.lagda)

| Shulman | Printed statement or assumptions | Weakening or correction |
| --- | --- | --- |
| Lemma 8.15 | Under LEM and C1, a set is discrete exactly when it has decidable equality. | Require the set and its sethood proof to be crisp for the equivalence. Under C1 and crisp LEM, ♭-discreteness is equivalent to decidable equality for such sets. Under $R♭$, decidable equality implies $\mathbb R$-nullness even for ordinary types, but the converse for every ordinary small set is false. Applied to $(0<x)\to\mathbf 2$, that converse would produce a nonconstant map $\mathbb R\to\mathbf 2$. [Agda correction](../typetopology/source/gist/RealCohesion/DiscreteSets.lagda) |
| Theorem 8.32 | LEM, C1 and T imply analytic Markov in its apartness and order forms. | LEM and T suffice for both forms. [nLab problem 2](#2-analytic-markovs-principle) explains why LEM and even $R♭$ do not suffice without T. |
| Theorem 11.2 | Exact intermediate values for a crisp function and crisp target under LEM, $R♭$ and T. | Drop T. Crisp decidability or totality of the real order also suffices in place of crisp LEM. $R♭$ may be weakened to C1 and mere NC. |
| Theorem 11.4 | Approximate intermediate values under $R♭$, for a crisp function and target. | Both may be ordinary. A rational witness exists under $R♭$, or under C1 and mere NC. |
| Theorem 11.5 | Continuity of a crisp real function at a crisp centre under $R♭$ and T. | $R♭$ alone suffices, in every crisp finite dimension, for **all ordinary nearby points**. C1 and mere NC suffice in place of $R♭$. |
| Corollary 11.6 | LEM, $R♭$ and T characterize the image of the map from crisp real functions. | Drop T and allow every crisp finite dimension. Injectivity and continuity of the values need only $R♭$. Crisp LEM gives the converse for all continuous functions on points. C1 and mere NC suffice in place of $R♭$. |
| Theorem 11.7 | LEM and $R♭$ refute analytic LLPO, the assertion that every real is nonnegative or nonpositive. | Drop LEM. More generally C1 and failure of ♭-discreteness of $\mathbb R$ already refute analytic LLPO. |
| Lemma 12.2 | Under univalence and $R♭$, the circle is not a retract of the disc. | A paper proof gives the no-retraction result in all positive finite dimensions under LEM and $R♭$, exchanging univalence for LEM. The cube version in Agda is a target with a conditional reduction. [Agda target](../typetopology/source/gist/RealCohesion/ShulmanWeakeningsStatements.lagda) |
| Lemma 12.3 | Under LEM, C1 and T, a fixed-point-free map of the disc makes the circle a retract of the disc. | Either LEM and T or LEM and C1 suffice. The result extends to every positive finite dimension, and the retraction can be taken to split the standard inclusion of the sphere into the ball. [Retraction statement](../typetopology/source/gist/RealCohesion/EuclideanSphere.lagda) |
| Theorem 12.4 | Under univalence, LEM, $R♭$ and T, every endomap of the disc sharply has a fixed point. | LEM, C1 and failure of ♭-discreteness of $\mathbb R$ suffice in every crisp finite dimension. The existence statement remains under ♯. [Sharp Brouwer](#the-two-classical-brouwer-fixed-point-theorems) |
| Corollary 12.5 | Under the same axioms every crisp endomap of the disc has a fixed point. | The same weaker axioms suffice in every crisp finite dimension. The fixed-point assertion for a crisp map holds in the ordinary mode. [Crisp Brouwer](#the-two-classical-brouwer-fixed-point-theorems) |
| Theorem 12.6 | Under univalence and $R♭$, every crisp endomap of the disc has an ordinary approximate fixed point. | For a crisp map of the square or disc, univalence, C1 and mere NC suffice. For an ordinary map, LEM, T and either $R♭$ or C1 with mere NC suffice in every crisp finite dimension. These are different statements. [Disc theorem for real errors](../typetopology/source/gist/RealCohesion/ApproximateBrouwerDisc.lagda) |

### Consequences for Myers's *Good fibrations through the modal prism*

The same distinctions about crisp variables affect several statements about the Dedekind reals and the shape modality. The following are paper results. [Myers, arXiv v4](https://arxiv.org/abs/1908.08034v4)

| Place in Myers | Correction or scope |
| --- | --- |
| Lemma 4.9(3) and Theorem 4.10 | The component argument needs decidable equality of the set of shape components $\int_0 X$. This holds, in particular, for crisp $X$. Corollary 9.14 retains its stated conclusion because the orbits of a permutation of a finite set have decidable equality. |
| Remark 6.5 | For the Dedekind reals the step from $r\ne0$ to positive apartness $r\mathrel{\#}0$ is analytic Markov. It can fail under LEM, $R♭$ and sharp choice. |
| Theorem 8.6 | Keep the printed crispness assumption on $X$. For an ordinary variable, the comparison with the separated reflection can fail already at $n=0$. In other models the relative shape of an $n$-connected ordinary type need not be $n$-connected for each $n\geq1$. The models satisfy LEM and $R♭$ and refute T. |
