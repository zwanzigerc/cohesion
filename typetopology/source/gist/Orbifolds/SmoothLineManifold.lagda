Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026 (local time). Orbifold gate H9 of Fable's
roadmap [1], following Fable's corrected guidance [2, Sections 1 and 4 C]
and GPT-6 Astra's audits [3, 4].

The smooth line is an ordinary manifold
---------------------------------------

The part of T5a that belongs to H9 [2, Section 1, item 4]: R, with its
metric topology, is an ordinary 1-dimensional manifold in the sense of
Definition 5.1.6 (module Manifolds), with centered charts and the
countable basis of open intervals with rational end points.

  smooth-line-topology : the metric topology of R. It is transported
  from the metric topology of R¹ = Fin 1 → R (Definition 5.1.4) along
  the coordinate equivalence R¹ ≃ R, v ↦ v 0 [4, Section 5]: U ⊆ R is
  open when {v | v 0 ∈ U} is metrically open, that is, when every
  x ∈ U has an ε > 0 with (x − y)² < ε² → y ∈ U. The coordinate
  equivalence is a homeomorphism, so regularity and T₀ come from
  Theorem 5.1.5;

  centered-charts-of-smooth-line : the chart at x is the translation
  v ↦ v 0 + x, defined on all of R¹, which contains the origin; it is a
  genuine open embedding, with continuity in both directions, and it
  takes the origin to x;

  rational-intervals-form-a-basis : the open intervals (⦅ p ⦆, ⦅ q ⦆)
  between rational points, indexed by ℕ through the enumeration of the
  module RationalPoints, form a basis of the topology, at every ordinary
  point of every open; this uses the density of the rational points
  twice. Each interval is homeomorphic to an open subset of R¹;

  smooth-line-is-an-ordinary-manifold : the structure of Definition
  5.1.6, at the universe 𝓤₀ of R.

The hypotheses are Postulate O, the translation law (from Postulate
Exp) and Postulate K. No chart, radius or rational is chosen for every
point: the witnesses are found inside propositions.

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026.
    references/F01-orbifolds-roadmap-rev2.md
[2] Claude Fable 5.2. Orbifolds H9 and H10: follow-up to Astra's
    readiness audits, 13 November 2026 (UTC).
    references/F04-orbifolds-h9-h10-followup.md
[3] GPT-6 Astra. Fable H10 readiness audit, 13 November 2026 (UTC).
    references/A17-h10-readiness-audit.txt
[4] GPT-6 Astra. H9 ordinary manifolds: statement prerequisites,
    13 November 2026 (UTC).
    references/A19-h9-manifold-prerequisites.txt

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module gist.Orbifolds.SmoothLineManifold where

open import Fin.Type
open import Naturals.Binary using (pairing)
open import UF.Base
open import UF.Equiv
open import UF.Subsingletons
open import UF.SubtypeClassifier
open import UF.UniverseEmbedding using (lift ; lower)
open import gist.Orbifolds.SmoothLine
open import gist.Orbifolds.SmoothOrder
open import gist.Orbifolds.SmoothOrderAlgebra
open import gist.Orbifolds.MetricTopology
open import gist.Orbifolds.RationalPoints
open import gist.Orbifolds.Manifolds

module smooth-line-manifold
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
        (𝓡 : Commutative-Ring)
       where

 open PropositionalTruncation pt
 open smooth-line fe pt 𝓡
 open smooth-order fe pt 𝓡
 open smooth-order-algebra fe pt 𝓡
 open metric-topology fe pt 𝓡
 open rational-points fe pt 𝓡
 open ordinary-manifolds fe pt 𝓡
 open import gist.Orbifolds.Topology fe pt
 open import gist.Orbifolds.Homeomorphisms fe pt

 module _ (O : Postulate-O) (translation : Translation-Law O) (K : Postulate-K)
        where

  open Postulate-O O
  open order-lemmas O translation
  open order-algebra O translation

  E : (n : ℕ) → Topology (Fin n → R) 𝓤₀
  E = Euclidean O translation K 𝓤₀

  distance : {n : ℕ} → (Fin n → R) → (Fin n → R) → R
  distance = squared-distance O translation K

  rational-value : Rational-Presentation → R
  rational-value = ⦅_⦆ O translation K

\end{code}

Order lemmas used below.

\begin{code}

  differences-reflect-order : (x u v : R) → x +ᴿ (-ᴿ u) < x +ᴿ (-ᴿ v) → v < u
  differences-reflect-order x u v l =
   transport₂ _<_ (negation-is-involutive v) (negation-is-involutive u)
    (negation-reverses-order (-ᴿ u) (-ᴿ v)
      (transport₂ _<_ (cancel u) (cancel v) (translation _ _ (-ᴿ x) l)))
   where
    cancel : (y : R) → x +ᴿ (-ᴿ y) +ᴿ (-ᴿ x) ＝ -ᴿ y
    cancel y = ap (_+ᴿ (-ᴿ x)) (+-comm x (-ᴿ y)) ∙ +-cancel' x (-ᴿ y)

  negation-of-difference : (x y : R) → -ᴿ (x +ᴿ (-ᴿ y)) ＝ y +ᴿ (-ᴿ x)
  negation-of-difference x y =
   negation-of-sum x (-ᴿ y) ∙ ap ((-ᴿ x) +ᴿ_) (negation-is-involutive y)
    ∙ +-comm (-ᴿ x) y

  below-difference-with-positive : (x e : R) → 0ᴿ < e → x +ᴿ (-ᴿ e) < x
  below-difference-with-positive x e l =
   transport₂ _<_ (+-comm (-ᴿ e) x) (+-unit-left x)
    (translation (-ᴿ e) 0ᴿ x (negation-of-positive-is-negative e l))

  difference-below-from-left : (x e y : R) → x +ᴿ (-ᴿ e) < y → x +ᴿ (-ᴿ y) < e
  difference-below-from-left x e y l =
   transport₂ _<_ (differences-compose y e x)
    (+-comm y (e +ᴿ (-ᴿ y)) ∙ +-cancel y e)
    (translation _ _ (e +ᴿ (-ᴿ y)) l)

  difference-above-from-right : (x e y : R) → y < x +ᴿ e → -ᴿ e < x +ᴿ (-ᴿ y)
  difference-above-from-right x e y l =
   transport (-ᴿ e <_) (negation-of-difference y x)
    (negation-reverses-order (y +ᴿ (-ᴿ x)) e
      (transport (y +ᴿ (-ᴿ x) <_) (ap (_+ᴿ (-ᴿ x)) (+-comm x e) ∙ +-cancel' x e)
        (translation _ _ (-ᴿ x) l)))

\end{code}

Translations of Rⁿ are homeomorphisms of the metric topology.

\begin{code}

  shift : {n : ℕ} → (Fin n → R) → (Fin n → R) → (Fin n → R)
  shift p v i = v i +ᴿ p i

  shifts-preserve-distance : {n : ℕ} (p v w : Fin n → R)
                           → distance (shift p v) (shift p w) ＝ distance v w
  shifts-preserve-distance p v w =
   ap ∑ (dfunext fe (λ i → ap₂ _·ᴿ_ (difference i) (difference i)))
   where
    difference : (i : Fin _)
               → (v i +ᴿ p i) +ᴿ (-ᴿ (w i +ᴿ p i)) ＝ v i +ᴿ (-ᴿ w i)
    difference i = ap ((v i +ᴿ p i) +ᴿ_) (negation-of-sum (w i) (p i))
                 ∙ +-interchange (v i) (p i) (-ᴿ w i) (-ᴿ p i)
                 ∙ ap (v i +ᴿ (-ᴿ w i) +ᴿ_) (+-inverse (p i))
                 ∙ +-unit _

  shifts-are-continuous : {n : ℕ} (p : Fin n → R)
                        → is-continuous (E n) (E n) (shift p)
  shifts-are-continuous p V oV =
   lift _ (λ v m → ∥∥-functor
                    (λ (ε , lε , f) → ε , lε ,
                       (λ w l → f (shift p w)
                                  (transport (_< ε ·ᴿ ε)
                                    ((shifts-preserve-distance p v w)⁻¹) l)))
                    (lower oV (shift p v) m))

  shifts-are-homeomorphisms : {n : ℕ} (p : Fin n → R)
                            → is-homeomorphism (E n) (E n) (shift p)
  shifts-are-homeomorphisms p =
   qinvs-are-equivs (shift p)
    (shift (λ i → -ᴿ p i) ,
     (λ v → dfunext fe (λ i → +-cancel' (p i) (v i))) ,
     (λ v → dfunext fe (λ i → +-cancel (p i) (v i)))) ,
   shifts-are-continuous p ,
   shifts-are-continuous (λ i → -ᴿ p i)

\end{code}

The coordinate equivalence and the topology of R.

\begin{code}

  coordinate : (Fin 1 → R) → R
  coordinate v = v 𝟎

  constant-vector : R → (Fin 1 → R)
  constant-vector x i = x

  coordinate-is-equiv : is-equiv coordinate
  coordinate-is-equiv =
   qinvs-are-equivs coordinate
    (constant-vector ,
     (λ v → dfunext fe (λ { 𝟎 → refl ; (suc ()) })) ,
     (λ x → refl))

  smooth-line-topology : Topology R 𝓤₀
  smooth-line-topology = final-topology coordinate (E 1)

  coordinate-is-homeomorphism
   : is-homeomorphism (E 1) smooth-line-topology coordinate
  coordinate-is-homeomorphism =
   equivalences-are-homeomorphisms-onto-final-topologies (E 1) coordinate
    coordinate-is-equiv

  smooth-line-topology-is-regular : is-regular smooth-line-topology
  smooth-line-topology-is-regular =
   regularity-is-invariant (E 1) smooth-line-topology coordinate
    coordinate-is-homeomorphism
    (metric-topology-is-regular O translation K)

  smooth-line-topology-is-T₀ : is-T₀ smooth-line-topology
  smooth-line-topology-is-T₀ =
   T₀-is-invariant (E 1) smooth-line-topology coordinate
    coordinate-is-homeomorphism
    (metric-topology-is-T₀ O translation K)

\end{code}

Centered charts: the translation v ↦ v 0 + x.

\begin{code}

  chart-at : R → (Fin 1 → R) → R
  chart-at x = coordinate ∘ shift (λ i → x)

  charts-are-homeomorphisms : (x : R)
   → is-homeomorphism (E 1) smooth-line-topology (chart-at x)
  charts-are-homeomorphisms x =
   ∘-is-homeomorphism (E 1) (E 1) smooth-line-topology (shift (λ i → x))
    coordinate
    (shifts-are-homeomorphisms (λ i → x)) coordinate-is-homeomorphism

  centered-charts-of-smooth-line : (x : R)
   → is-centered-chart-at O translation K 1 smooth-line-topology x
  centered-charts-of-smooth-line x =
   ∣ full , Topology.full-is-open (E 1) , ⋆ , φ ,
     ∣ full , (λ _ → ⋆) , Topology.full-is-open smooth-line-topology ,
       restrictions-of-homeomorphisms-to-subspaces (E 1) smooth-line-topology
        (chart-at x) (charts-are-homeomorphisms x) full ∣ ,
     +-unit-left x ∣
   where
    φ : 𝕊 (E 1) full → R
    φ w = chart-at x (pr₁ w)

\end{code}

Open intervals, and the rational intervals as a basis.

\begin{code}

  interval : R → R → Subset R 𝓤₀
  interval a b y =
   ((a < y) × (y < b)) , ×-is-prop (<-is-prop-valued a y) (<-is-prop-valued y b)

  intervals-are-open : (a b : R)
                     → Topology.is-open smooth-line-topology (interval a b)
  intervals-are-open a b =
   lift _ (λ v (la , lb) →
            let x = v 𝟎
                η = positive-below-two K (x +ᴿ (-ᴿ a)) (b +ᴿ (-ᴿ x))
                     (difference-is-positive a x la)
                      (difference-is-positive x b lb)
                ε = pr₁ η
                lε = pr₁ (pr₂ η)
                ε<x-a = pr₁ (pr₂ (pr₂ η))
                ε<b-x = pr₂ (pr₂ (pr₂ η))
            in ∣ ε , lε ,
                 (λ w l →
                   let box = ball-in-box O translation K v w ε lε l 𝟎
                   in differences-reflect-order x (w 𝟎) a
                    (<-is-transitive _ _ _ (pr₂ box) ε<x-a) ,
                      differences-reflect-order x b (w 𝟎)
                       (<-is-transitive _ _ _
                         (transport (_< -ᴿ ε) (negation-of-difference b x)
                           (negation-reverses-order ε (b +ᴿ (-ᴿ x)) ε<b-x))
                         (pr₁ box))) ∣)

  endpoints : ℕ → Rational-Presentation × Rational-Presentation
  endpoints n = rational-presentation-of (pr₁ (unpair n)) ,
                rational-presentation-of (pr₂ (unpair n))

  code-of-endpoints : Rational-Presentation → Rational-Presentation → ℕ
  code-of-endpoints p q = ⌜ pairing ⌝ (code-of-rational-presentation p ,
                                       code-of-rational-presentation q)

  endpoints-of-code : (p q : Rational-Presentation)
                    → endpoints (code-of-endpoints p q) ＝ (p , q)
  endpoints-of-code p q =
   ap
    (λ c → rational-presentation-of (pr₁ c) , rational-presentation-of (pr₂ c))
      (unpair-pair
        (code-of-rational-presentation p , code-of-rational-presentation q))
   ∙ ap₂ _,_ (rational-presentation-of-code p) (rational-presentation-of-code q)

  rational-interval : ℕ → Subset R 𝓤₀
  rational-interval n = interval (rational-value (pr₁ (endpoints n)))
                         (rational-value (pr₂ (endpoints n)))

  rational-intervals-form-a-basis
   : is-basis smooth-line-topology rational-interval
  rational-intervals-form-a-basis =
   (λ n → intervals-are-open (rational-value (pr₁ (endpoints n)))
           (rational-value (pr₂ (endpoints n)))) ,
   refine
   where
    refine : (U : Subset R 𝓤₀) → Topology.is-open smooth-line-topology U
           → (x : R) → x ∈ U
           → ∃ n ꞉ ℕ , x ∈ rational-interval n × rational-interval n ⊆ U
    refine U oU x xU =
     ∥∥-rec ∃-is-prop
      (λ (ε , lε , ball) →
        ∥∥-rec ∃-is-prop
         (λ (p , lp , pl) →
           ∥∥-functor
            (λ (q , lq , ql) →
              let n = code-of-endpoints p q
                  same : rational-interval n
                       ＝ interval (rational-value p) (rational-value q)
                  same = ap (λ e →
                    interval (rational-value (pr₁ e)) (rational-value (pr₂ e)))
                          (endpoints-of-code p q)
              in n ,
                 transport (x ∈_) (same ⁻¹) (pl , lq) ,
                 (λ y m → let (py , yq) = transport (y ∈_) same m
                          in ball (constant-vector y)
                              (transport (_< ε ·ᴿ ε) ((+-unit-left _)⁻¹)
                                (square-from-interval ε (x +ᴿ (-ᴿ y))
                                  (difference-above-from-right x ε y
                                    (<-is-transitive _ _ _ yq ql))
                                  (difference-below-from-left x ε y
                                    (<-is-transitive _ _ _ lp py))))))
            (rational-points-are-dense O translation K x (x +ᴿ ε)
              (below-sum-with-positive O translation K x ε lε)))
         (rational-points-are-dense O translation K (x +ᴿ (-ᴿ ε)) x
           (below-difference-with-positive x ε lε)))
      (lower oU (constant-vector x) xU)

  rational-intervals-are-chart-domains
   : (n : ℕ) → is-Euclidean-chart-domain O translation K 1 smooth-line-topology
     (rational-interval n)
  rational-intervals-are-chart-domains n =
   ∣ (λ v → rational-interval n (coordinate v)) ,
     intervals-are-open (rational-value (pr₁ (endpoints n)))
      (rational-value (pr₂ (endpoints n))) ,
     restriction-to-preimage (E 1) smooth-line-topology coordinate
      coordinate-is-homeomorphism
      (rational-interval n) ,
     restrictions-of-homeomorphisms-to-subspaces (E 1) smooth-line-topology
      coordinate
      coordinate-is-homeomorphism (rational-interval n) ∣

\end{code}

Definition 5.1.6 for R.

\begin{code}

  smooth-line-is-an-ordinary-manifold : Ordinary-Manifold O translation K 1 R
  smooth-line-is-an-ordinary-manifold = record
   { carrier-is-set = R-is-set
    ; topology = smooth-line-topology
    ; topology-is-regular = smooth-line-topology-is-regular
    ; topology-is-T₀ = smooth-line-topology-is-T₀
    ; charts = centered-charts-of-smooth-line
    ; basis = rational-interval
    ; basis-is-basis = rational-intervals-form-a-basis
    ; basis-consists-of-chart-domains = rational-intervals-are-chart-domains
    }

\end{code}
