Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 13 November 2026 (local time); the proof of
nilsquares-cannot-all-vanish moved to gist.Orbifolds.DualNumbers later
that day, in the consolidation after the final audits, so that this
module no longer imports the groupoid example of T5a
(gist.Orbifolds.SmoothLineGroupoid). Orbifold gate H10 of Fable's
roadmap [1], for the target T5b, following GPT-6 Astra's proof [2,
Section 4] and preflight [3, Section D].

ℑ-modal ordinary manifolds have open singletons
-----------------------------------------------

Let M be an ordinary manifold of dimension n (Manifolds) whose lift to
the universe of ℑ is ℑ-modal. At every ordinary point p:

  modal-manifolds-have-open-singletons : {p} is open. Take a chart at
  p: an open U ⊆ Rⁿ containing the origin and an open embedding
  φ : U ↪ M with φ(0) = p, opened inside the proposition. If n is a
  successor, then for d in the spectrum of the fixed crisp dual numbers
  R[ε]/(ε²), the point d·e₁ is ¬¬-equal to the origin (K), so lies in U
  (Lemma 5.1.3 for the metric topology); since M is ℑ-modal, the map
  d ↦ φ(d·e₁) from the generator is constant, and φ is injective, so
  every nilsquare is 0, which the injectivity half of J for the dual
  numbers forbids (nilsquares-cannot-all-vanish). So n = 0; then the
  image of φ, an open set, is the singleton {p};

  modal-manifolds-have-decidable-equality : {p} is open, so Penon open
  by regularity (Lemma 6.2.7), so y ＝ p or y ≠ p.

The conclusion is pointwise: an empty manifold of any dimension is
allowed, and no global claim n = 0 is made [3, Section D].

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026.
    references/F01-orbifolds-roadmap-rev2.md
[2] GPT-6 Astra. DP properness implies the replacement over the
    five-item core, 11 November 2026.
    references/A02-dp-properness-implies-replacement.txt
[3] GPT-6 Astra. H10 T5b implementation preflight, 13 November 2026
    (UTC).
    references/A24-t5b-preflight.txt

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import Modal.Subuniverse
open import gist.Orbifolds.SmoothLine
 using (Commutative-Ring ; module smooth-line)

module gist.Orbifolds.ZeroDimensionalCharts
        (@♭ fe : Fun-Ext)
        (@♭ pt : propositional-truncations-exist)
        (@♭ 𝓡 : Commutative-Ring)
        {@♭ 𝓤 : Universe}
       where

open import Fin.Type
open import UF.Base
open import UF.DiscreteAndSeparated using (is-discrete)
open import UF.Equiv
open import UF.Sets
open import UF.Sets-Properties using (Σ-is-set ; Π-is-set)
open import UF.Subsingletons-FunExt
open import UF.Subsingletons-Properties using (props-are-sets)
open import UF.SubtypeClassifier
open import UF.UniverseEmbedding using (Lift ; lift ; lower)
open import gist.CohesiveApartness.Flat using (_^♭)
open import gist.Orbifolds.SmoothOrder
open import gist.Orbifolds.MetricTopology
open import gist.Orbifolds.Manifolds

open PropositionalTruncation pt
open smooth-line fe pt 𝓡
open smooth-order fe pt 𝓡
open metric-topology fe pt 𝓡 using (metric-topology-is-regular)
open ordinary-manifolds fe pt 𝓡
open import gist.Orbifolds.Topology fe pt
import gist.Orbifolds.DualNumbers
open import gist.Orbifolds.Microlinearity fe pt 𝓡 {𝓤 ⁺}
 using (ℑ-generator ; ℑ-generator-point)
open import gist.Orbifolds.Nullification fe
 using (is-nullification ; maps-from-generators-to-modal-types-are-constant)

private
 module DN = gist.Orbifolds.DualNumbers fe pt 𝓡

open DN using (dual-numbers ; Postulate-J-for-dual-numbers)

module _ (O : Postulate-O) (Exp : Postulate-Exp O) (K : Postulate-K)
         (J : Postulate-J-for-dual-numbers)
         {𝓟 : Universe}
         (P : subuniverse (𝓤 ⁺) 𝓟)
         (P-is-reflective : subuniverse-is-reflective P)
         (ν : is-nullification ℑ-generator ℑ-generator-point P)
       where

 private
  translation : Translation-Law O
  translation = translation-law-from-Exp O Exp

  E : (k : ℕ) → Topology (Fin k → R) 𝓤
  E = Euclidean O translation K 𝓤

\end{code}

The nilsquares cannot all vanish: the contradiction of
gist.Orbifolds.DualNumbers, which the proof that the anchor of the
unit pregroupoid is not Dubuc–Penon proper also uses, named here by a
typed alias with the parameters of this module.

\begin{code}

 nilsquares-cannot-all-vanish : ((d : Spec dual-numbers) → pr₁ d 𝟎 ＝ 0ᴿ) → 𝟘
 nilsquares-cannot-all-vanish = DN.nilsquares-cannot-all-vanish K J

\end{code}

Charts of an ℑ-modal manifold.

\begin{code}

 module _ {n : ℕ} {M : 𝓤 ̇ } (𝓜 : Ordinary-Manifold O translation K n M)
          (M-is-modal : subuniverse-contains P (Lift (𝓤 ⁺) M))
        where

  open Ordinary-Manifold 𝓜

  singleton : M → Subset M 𝓤
  singleton p y = (y ＝ p) , carrier-is-set

  private
   open-embeddings-are-left-cancellable
    : {k : ℕ} (U : Subset (Fin k → R) 𝓤) (φ : 𝕊 (E k) U → M)
    → is-open-embedding (subspace (E k) U) topology φ
    → {w w' : 𝕊 (E k) U} → φ w ＝ φ w' → w ＝ w'
   open-embeddings-are-left-cancellable U φ oe {w} {w'} p =
    ∥∥-rec (Σ-is-set (Π-is-set fe (λ _ → R-is-set))
             (λ x → props-are-sets (∈-is-prop x U)))
     (λ (V , m , oV , (e , _ , _)) →
       equivs-are-lc (corestriction (subspace (E _) U) topology φ V m) e
        (to-subtype-＝ (λ y → ∈-is-prop y V) p))
     oe

   vector : (k : ℕ) → Spec dual-numbers → (Fin (succ k) → R)
   vector k d 𝟎 = pr₁ d 𝟎
   vector k d (suc i) = 0ᴿ

   vectors-are-infinitesimal : (k : ℕ) (d : Spec dual-numbers)
                             → ¬¬ (vector k d ＝ (origin O translation K))
   vectors-are-infinitesimal k d =
    ¬¬-functor
     (λ (q : pr₁ d 𝟎 ＝ 0ᴿ) → dfunext fe (λ { 𝟎 → q ; (suc i) → refl }))
     (nilpotents-are-infinitesimal K (pr₁ d 𝟎)
       (2 , (ap (_·ᴿ pr₁ d 𝟎) (·-unit-left (pr₁ d 𝟎)) ∙ pr₂ d 𝟎)))

   positive-dimension-is-impossible
    : (k : ℕ) (U : Subset (Fin (succ k) → R) 𝓤)
    → Topology.is-open (E (succ k)) U
    → (origin O translation K) ∈ U
    → (φ : 𝕊 (E (succ k)) U → M)
    → is-open-embedding (subspace (E (succ k)) U) topology φ
    → 𝟘
   positive-dimension-is-impossible k U oU z φ oe =
    nilsquares-cannot-all-vanish
     (λ d → happly (ap pr₁
       (open-embeddings-are-left-cancellable U φ oe (ap lower (constant d)))) 𝟎)
    where
     in-U : (d : Spec dual-numbers) → vector k d ∈ U
     in-U d = opens-of-regular-spaces-are-infinitesimally-stable (E (succ k))
               (metric-topology-is-regular O translation K) U oU
                (origin O translation K) (vector k d) z
               (vectors-are-infinitesimal k d)

     h : Lift (𝓤 ⁺) (Spec dual-numbers) → Lift (𝓤 ⁺) M
     h w = lift (𝓤 ⁺) (φ (vector k (lower w) , in-U (lower w)))

     constant : (d : Spec dual-numbers)
              → lift (𝓤 ⁺) (φ (vector k d , in-U d))
              ＝ lift (𝓤 ⁺) (φ (vector k (Spec-point dual-numbers) ,
                                in-U (Spec-point dual-numbers)))
     constant d = maps-from-generators-to-modal-types-are-constant ℑ-generator
                   ℑ-generator-point P ν
                   (Lift (𝓤 ⁺) M) M-is-modal (dual-numbers ^♭) h (lift (𝓤 ⁺) d)

   zero-dimensional-images-are-singletons
    : (U : Subset (Fin 0 → R) 𝓤) (z : (origin O translation K) ∈ U)
      (φ : 𝕊 (E 0) U → M)
    → (V : Subset M 𝓤) (m : (w : 𝕊 (E 0) U) → φ w ∈ V)
    → is-equiv (corestriction (subspace (E 0) U) topology φ V m)
    → (p : M) → φ ((origin O translation K) , z) ＝ p
    → (y : M) → (y ∈ V → y ＝ p) × (y ＝ p → y ∈ V)
   zero-dimensional-images-are-singletons U z φ V m e p q y =
    (λ yV → ap pr₁ ((inverses-are-sections c e (y , yV))⁻¹)
            ∙ ap φ (to-subtype-＝ (λ x → ∈-is-prop x U) (dfunext fe (λ ())))
            ∙ q) ,
    (λ r → transport (_∈ V) (q ∙ r ⁻¹) (m ((origin O translation K) , z)))
    where
     c = corestriction (subspace (E 0) U) topology φ V m

   open-singletons-from-charts
    : (k : ℕ) (p : M) (U : Subset (Fin k → R) 𝓤) → Topology.is-open (E k) U
    → (z : (origin O translation K) ∈ U) (φ : 𝕊 (E k) U → M)
    → is-open-embedding (subspace (E k) U) topology φ
    → φ ((origin O translation K) , z) ＝ p
    → Topology.is-open topology (singleton p)
   open-singletons-from-charts 0 p U oU z φ oe q =
    ∥∥-rec (Topology.being-open-is-prop topology (singleton p))
     (λ (V , m , oV , (e , _ , _)) →
       Topology.openness-is-extensional topology V (singleton p)
        (λ y yV →
          pr₁ (zero-dimensional-images-are-singletons U z φ V m e p q y) yV)
        (λ y r →
          pr₂ (zero-dimensional-images-are-singletons U z φ V m e p q y) r)
        oV)
     oe
   open-singletons-from-charts (succ k) p U oU z φ oe q =
    𝟘-elim (positive-dimension-is-impossible k U oU z φ oe)

  modal-manifolds-have-open-singletons : (p : M)
                                       → Topology.is-open topology (singleton p)
  modal-manifolds-have-open-singletons p =
   ∥∥-rec (Topology.being-open-is-prop topology (singleton p))
    (λ (U , oU , z , φ , oe , q) →
      open-singletons-from-charts n p U oU z φ oe q)
    (charts p)

  modal-manifolds-have-decidable-equality : is-discrete M
  modal-manifolds-have-decidable-equality p y =
   ∥∥-rec (decidability-of-prop-is-prop fe carrier-is-set)
    (cases (λ ne → inr ne) (λ (r : y ＝ p) → inl (r ⁻¹)))
    (opens-of-manifolds-are-Penon-open O translation K 𝓜 (singleton p)
      (modal-manifolds-have-open-singletons p) p refl y)

\end{code}
