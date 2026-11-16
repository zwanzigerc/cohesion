Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026 (local time). Orbifold gate H9 of Fable's
roadmap [1], following Fable's corrected guidance [2, Sections 1 and 4 C]
and GPT-6 Astra's audits [3, 4].

Ordinary manifolds: Myers's Definition 5.1.6
--------------------------------------------

Myers [5, Definition 5.1.6, pp. 42–43] defines an ordinary n-dimensional
manifold M as a regular Hausdorff (regular and T₀) topological space such
that every point p merely has a chart around p: an open subset U of Rⁿ
containing the origin and an open embedding φ : U ↪ M with φ(0) = p.
Ordinary manifolds are assumed second countable, "in that they have a
countable base of charts". Here, for a carrier M in a universe 𝓤 with
open subsets valued in 𝓤:

  Ordinary-Manifold n M : the structure. Its fields are that M is a set,
  a topology on M, regularity and T₀, the centered charts (a mere chart
  at every point, with the metric topology of Rⁿ of Theorem 5.1.5 and
  the genuine open embeddings of the module Topology), and the countable
  basis of charts as data: a family ℕ → Subset M 𝓤 that is a basis of
  the topology, each member of which is merely homeomorphic to an open
  subset of Rⁿ, for the subspace topologies.

The dimension n is fixed, as in the paper; it may be 0, and M may be
empty. Members of the basis may be empty. No chart map is chosen for a
member of the basis; only the mere existence of one is assumed, which is
what the sum of the charts uses [2, Section 2, step 3]. Decidable
equality is not assumed. Setness is a field: the arguments with
injective charts need it, and it is not derived from T₀ [4, Section 2].
The record itself is ordinary, and so are the topologies. In the final
theorems T1 and T5 the crisp data are the pregroupoid, hence its
carriers, and the basis of its arrows; the topologies, the basis of the
objects, the dimensions and all laws are ordinary arguments, and the
record is assembled ordinarily (Ordinary-Manifold-Laws below). The whole
record is never a crisp argument, which would make every field crisp
[4; 6]. The version with crisp topologies is a specialization.

Derived here: local openness from the basis (Astra's argument [3]),
Hausdorffness (Lemma 5.1.2), and stability of opens under ¬¬-equality
(Lemma 5.1.3).

The metric topology needs Postulate O, the translation law (from
Postulate Exp) and Postulate K, so the definition is relative to them.

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026.
    references/F01-orbifolds-roadmap-rev2.md
[2] Claude Fable 5.2. Orbifolds H9 and H10: follow-up to Astra's
    readiness audits, 13 November 2026 (UTC).
    references/F04-orbifolds-h9-h10-followup.md
[3] GPT-6 Astra. H9 topology universe and fidelity provisional audits,
    13 November 2026 (UTC).
    references/A21-h9-topology-universe-audit.txt
    references/A22-h9-topology-fidelity-audit.txt
[4] GPT-6 Astra. H9 ordinary manifolds: statement prerequisites,
    13 November 2026 (UTC).
    references/A19-h9-manifold-prerequisites.txt
[5] D. J. Myers. Orbifolds as microlinear types in synthetic
    differential cohesive homotopy type theory. arXiv:2205.15887v1.
[6] GPT-6 Astra. Focused manifold crispness release, 13 November 2026
    (UTC), with Claude Fable 5.2's reply on crispness of the same day.
    references/A28-manifold-crispness-release.txt

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module gist.Orbifolds.Manifolds where

open import Fin.Type
open import UF.Sets
open import UF.Subsingletons
open import UF.SubtypeClassifier
open import gist.Orbifolds.SmoothLine
open import gist.Orbifolds.SmoothOrder
open import gist.Orbifolds.MetricTopology

module ordinary-manifolds
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
        (𝓡 : Commutative-Ring)
       where

 open PropositionalTruncation pt
 open smooth-line fe pt 𝓡
 open smooth-order fe pt 𝓡
 open metric-topology fe pt 𝓡
 open import gist.Orbifolds.Topology fe pt
 open import gist.Orbifolds.CoverFiniteness fe pt using (is-Penon-open)

 module _ (O : Postulate-O) (translation : Translation-Law O) (K : Postulate-K)
        where

\end{code}

Euclidean space with the metric topology, and charts.

\begin{code}

  Euclidean : (𝓤 : Universe) (n : ℕ) → Topology (Fin n → R) 𝓤
  Euclidean 𝓤 n = metric-topology O translation K 𝓤 n

  origin : {n : ℕ} → Fin n → R
  origin i = 0ᴿ

  is-centered-chart-at : {𝓤 : Universe} (n : ℕ) {M : 𝓤 ̇ } → Topology M 𝓤 → M
                       → 𝓤 ⁺ ̇
  is-centered-chart-at {𝓤} n {M} T p =
   ∃ U ꞉ Subset (Fin n → R) 𝓤 ,
    Σ oU ꞉ Topology.is-open (Euclidean 𝓤 n) U ,
    Σ z ꞉ origin ∈ U ,
    Σ φ ꞉ (𝕊 (Euclidean 𝓤 n) U → M) ,
       is-open-embedding (subspace (Euclidean 𝓤 n) U) T φ
     × (φ (origin , z) ＝ p)

  is-Euclidean-chart-domain : {𝓤 : Universe} (n : ℕ) {M : 𝓤 ̇ }
                            → (T : Topology M 𝓤) → Subset M 𝓤 → 𝓤 ⁺ ̇
  is-Euclidean-chart-domain {𝓤} n {M} T B =
   ∃ V ꞉ Subset (Fin n → R) 𝓤 ,
    Σ oV ꞉ Topology.is-open (Euclidean 𝓤 n) V ,
    Σ h ꞉ (𝕊 (Euclidean 𝓤 n) V → 𝕊 T B) ,
       is-homeomorphism (subspace (Euclidean 𝓤 n) V) (subspace T B) h

\end{code}

Definition 5.1.6.

\begin{code}

  record Ordinary-Manifold {𝓤 : Universe} (n : ℕ) (M : 𝓤 ̇ ) : 𝓤 ⁺ ⁺ ̇ where
   field
    carrier-is-set : is-set M
    topology : Topology M 𝓤
    topology-is-regular : is-regular topology
    topology-is-T₀ : is-T₀ topology
    charts : (p : M) → is-centered-chart-at n topology p
    basis : ℕ → Subset M 𝓤
    basis-is-basis : is-basis topology basis
    basis-consists-of-chart-domains : (i : ℕ)
     → is-Euclidean-chart-domain n topology (basis i)

\end{code}

The same structure with the carrier, topology and basis given, and only
the laws as a record: the form in which the final theorems take the
manifold of arrows, whose carrier and basis are crisp there, while its
topology and laws are ordinary [6].

\begin{code}

  record Ordinary-Manifold-Laws {𝓤 : Universe} (n : ℕ) {M : 𝓤 ̇ }
                                (T : Topology M 𝓤) (B : ℕ → Subset M 𝓤) : 𝓤 ⁺ ̇
                                 where
   field
    carrier-is-set : is-set M
    topology-is-regular : is-regular T
    topology-is-T₀ : is-T₀ T
    charts : (p : M) → is-centered-chart-at n T p
    basis-is-basis : is-basis T B
    basis-consists-of-chart-domains : (i : ℕ)
                                    → is-Euclidean-chart-domain n T (B i)

  manifold-from-laws : {𝓤 : Universe} {n : ℕ} {M : 𝓤 ̇ }
                       (T : Topology M 𝓤) (B : ℕ → Subset M 𝓤)
                     → Ordinary-Manifold-Laws n T B → Ordinary-Manifold n M
  manifold-from-laws T B L = record
   { carrier-is-set = carrier-is-set
    ; topology = T
    ; topology-is-regular = topology-is-regular
    ; topology-is-T₀ = topology-is-T₀
    ; charts = charts
    ; basis = B
    ; basis-is-basis = basis-is-basis
    ; basis-consists-of-chart-domains = basis-consists-of-chart-domains
    }
   where
    open Ordinary-Manifold-Laws L

\end{code}

Consequences: local openness, Lemma 5.1.2 and Lemma 5.1.3.

\begin{code}

  module _ {𝓤 : Universe} {n : ℕ} {M : 𝓤 ̇ } (𝓜 : Ordinary-Manifold n M) where

   open Ordinary-Manifold 𝓜

   manifold-topology-has-local-openness : has-local-openness topology
   manifold-topology-has-local-openness =
    based-topologies-have-local-openness topology basis basis-is-basis

   manifold-topology-is-regular-Hausdorff : is-regular-Hausdorff topology
   manifold-topology-is-regular-Hausdorff = topology-is-regular , topology-is-T₀

   manifold-topology-is-Hausdorff : is-Hausdorff topology
   manifold-topology-is-Hausdorff =
    regular-Hausdorff-spaces-are-Hausdorff topology
     manifold-topology-is-regular-Hausdorff

   opens-of-manifolds-are-infinitesimally-stable
    : (U : Subset M 𝓤) → Topology.is-open topology U
    → (x y : M) → x ∈ U → ¬¬ (y ＝ x) → y ∈ U
   opens-of-manifolds-are-infinitesimally-stable =
    opens-of-regular-spaces-are-infinitesimally-stable topology
     topology-is-regular

   opens-of-manifolds-are-Penon-open
    : (U : Subset M 𝓤) → Topology.is-open topology U
    → is-Penon-open (λ x → x ∈ U)
   opens-of-manifolds-are-Penon-open =
    opens-of-regular-spaces-are-Penon-open topology topology-is-regular

\end{code}
