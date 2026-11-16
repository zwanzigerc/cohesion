Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026 (local time); the proof of
chart-indices-are-♭-discrete shared with
gist.RealCohesion.PunctualCohesion, 13 November 2026, in the
consolidation after the final audits. Orbifold gate H9 of Fable's
roadmap [1, Sections 3.6 and 3.9], with GPT-6 Astra's audits [2, 3, 4].

The chart index, and the bridge from ordinary charts
----------------------------------------------------

Let s : X → Y be an ordinary local homeomorphism between sets with
regular topologies (the genuine predicate of the module Topology), and
B : ℕ → Subset X 𝓤 a basis of the topology of X. The chart index is the
subtype of ℕ cut out by the proposition "s is injective on B n" [2,
Section 4 (a)].

  Chart-Index s B, chart : the index and its family of basic opens;

  chart-indices-are-♭-discrete : for crisp X, Y, s and B, the index is
  ♭-discrete, by Axiom C1: ℕ is ♭-discrete (CrispInduction), so null
  for every generator; maps from a generator into the index are then
  constant in their first component, hence constant; so the index is
  null for every generator, and ♭-discrete by C0. This is Astra's route
  [3]; no decision and no crisp proof of setness is needed;

  chart-indices-are-discrete, charts-cover, s-is-injective-on-charts,
  charts-are-Penon-open : the properties that CoverFiniteness asks for
  [4, Sections 1–3]. The charts cover when s is locally injective
  (is-locally-injective, the hypothesis of the helper T1′), because B
  is a basis; local homeomorphisms are locally injective;

  source-maps-of-local-homeomorphisms-are-étale : the bridge 3.9 [1]:
  s, lifted to the universe 𝓤 ⁺ of the modality, is ℑ-étale. The sum of
  the charts over the lifted index, which is ℑ-modal by K because its
  equality is decidable, maps onto X étale (Lemma B for each chart,
  which is open in a regular space; Myers's Lemma 5.3.3). On each chart
  s is a genuine open embedding (LocalHomeomorphisms, the injective
  case), so s composed with the inclusion of a chart is an equivalence
  followed by the inclusion of an open of Y, which is étale; summing,
  s composed with the sum map is étale; and s is étale by Lemma D.

No chart map is chosen: open embeddings are used inside the
proposition that a map is étale.

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026.
    references/F01-orbifolds-roadmap-rev2.md
[2] GPT-6 Astra. H9 topology universe provisional audit, 13 November
    2026 (UTC).
    references/A21-h9-topology-universe-audit.txt
[3] GPT-6 Astra. H9 chart index: minimal native flat-discreteness
    reuse, 13 November 2026 (UTC).
    references/A20-h9-chart-index.txt
[4] GPT-6 Astra. Main aim: finiteness from the current open-cover
    properness condition, 11 November 2026.
    references/A03-cover-finiteness.txt

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import Modal.Subuniverse
open import gist.Orbifolds.SmoothLine
 using (Commutative-Ring ; module smooth-line)

module gist.Orbifolds.EtaleSourceMaps
        (@♭ fe : Fun-Ext)
        (@♭ pt : propositional-truncations-exist)
        (@♭ 𝓡 : Commutative-Ring)
        {@♭ 𝓤 : Universe}
       where

open import UF.Base
open import UF.Equiv
open import UF.Equiv-FunExt using (being-equiv-is-prop)
open import UF.DiscreteAndSeparated using (is-discrete)
open import UF.ImageAndSurjection pt using (is-surjection)
open import UF.Sets
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import UF.UniverseEmbedding using (Lift ; lift ; lower ; Lift-≃)
open import gist.CohesiveApartness.Flat
 using (is-♭-discrete ; Axiom-C1)
open import gist.CohesiveApartness.CrispInduction using (𝟚-is-♭-discrete)
import gist.RealCohesion.PunctualCohesion

open PropositionalTruncation pt
open smooth-line fe pt 𝓡
open import gist.Orbifolds.Topology fe pt
open import gist.Orbifolds.LocalHomeomorphisms fe pt
 using (injective-local-homeomorphisms-are-open-embeddings)
open import gist.Orbifolds.CoverFiniteness fe pt
 using (is-Penon-open ; is-injective-on-charts)
open import gist.Orbifolds.CrispCoverFiniteness fe pt {𝓤}
 using (subtypes-of-ℕ-are-discrete)
open import gist.Orbifolds.Microlinearity fe pt 𝓡 {𝓤 ⁺}
 using (ℑ-generator ; ℑ-generator-point ; discrete-types-are-ℑ-modal)
open import gist.Orbifolds.Nullification fe
 using
  (is-nullification ; nullifications-are-Σ-closed ; nullifications-are-replete ;
   propositions-are-modal)
open import gist.Orbifolds.ManifoldMicrolinearity fe pt 𝓡 {𝓤}
 using (stable-subtype-equivalence ; sums-of-étale-maps-are-étale)

\end{code}

The chart index.

\begin{code}

module _ {X Y : 𝓤 ̇ } (s : X → Y) where

 is-injective-on : Subset X 𝓤 → 𝓤 ̇
 is-injective-on C = (x x' : X) → x ∈ C → x' ∈ C → s x ＝ s x' → x ＝ x'

 is-locally-injective : Topology X 𝓤 → 𝓤 ⁺ ̇
 is-locally-injective T =
  (x : X) → ∃ U ꞉ Subset X 𝓤 , Topology.is-open T U × x ∈ U × is-injective-on U

 local-homeomorphisms-are-locally-injective
  : (T : Topology X 𝓤) (T' : Topology Y 𝓤)
  → is-local-homeomorphism T T' s → is-locally-injective T
 local-homeomorphisms-are-locally-injective T T' l x =
  ∥∥-functor
   (λ (U , V , m , oU , oV , xU , sxV , H) →
     U , oU , xU ,
     (λ x₁ x₂ m₁ m₂ q →
       ap pr₁
        (equivs-are-lc (restriction T T' s U V m) (pr₁ H) {x₁ , m₁} {x₂ , m₂}
          (to-subtype-＝ (λ y → ∈-is-prop y V) q))))
   (l x)

module _ {X Y : 𝓤 ̇ } (s : X → Y) (B : ℕ → Subset X 𝓤) where

 Chart-Index : 𝓤 ̇
 Chart-Index = Σ n ꞉ ℕ , is-injective-on s (B n)

 chart : Chart-Index → Subset X 𝓤
 chart j = B (pr₁ j)

 s-is-injective-on-charts : is-injective-on-charts s (λ j x → x ∈ chart j)
 s-is-injective-on-charts j = pr₂ j

 module _ (X-is-set : is-set X) where

  being-injective-on-is-prop : (C : Subset X 𝓤) → is-prop (is-injective-on s C)
  being-injective-on-is-prop C =
   Π₅-is-prop fe (λ _ _ _ _ _ → X-is-set)

  chart-indices-are-discrete : is-discrete Chart-Index
  chart-indices-are-discrete =
   subtypes-of-ℕ-are-discrete (λ n → is-injective-on s (B n))
    (λ n → being-injective-on-is-prop (B n))

 module _ (T : Topology X 𝓤) where

  charts-are-open : is-basis T B → (j : Chart-Index)
                  → Topology.is-open T (chart j)
  charts-are-open b j = pr₁ b (pr₁ j)

  charts-cover : is-locally-injective s T → is-basis T B
               → (x : X) → ∃ j ꞉ Chart-Index , x ∈ chart j
  charts-cover l b x =
   ∥∥-rec ∃-is-prop
    (λ (U , oU , xU , i) →
      ∥∥-functor
       (λ (n , xBn , Bn⊆U) →
         (n , (λ x₁ x₂ m₁ m₂ q → i x₁ x₂ (Bn⊆U x₁ m₁) (Bn⊆U x₂ m₂) q)) , xBn)
       (pr₂ b U oU x xU))
    (l x)

  charts-are-Penon-open : is-regular T → is-basis T B
                        → (j : Chart-Index) → is-Penon-open (λ x → x ∈ chart j)
  charts-are-Penon-open r b j =
   opens-of-regular-spaces-are-Penon-open T r (chart j) (charts-are-open b j)

\end{code}

The chart index is ♭-discrete, by Axiom C1: it has decidable equality
(chart-indices-are-discrete), and a crisp type with decidable equality
is ♭-discrete under Axiom C1 (gist.RealCohesion.PunctualCohesion, with
the ♭-discreteness of 𝟚 from gist.CohesiveApartness.CrispInduction).
Before the consolidation of 13 November 2026 this proof repeated that
argument, testing the first component with maps into ℕ; the type and
the universe are unchanged.

\begin{code}

chart-indices-are-♭-discrete
 : {𝓙 𝓖 : Universe} {J : 𝓙 ̇ } {Gen : J → 𝓖 ̇ } → Axiom-C1 Gen
 → {@♭ X Y : 𝓤 ̇ } (@♭ s : X → Y) (@♭ B : ℕ → Subset X 𝓤)
 → is-set X
 → is-♭-discrete (Chart-Index s B)
chart-indices-are-♭-discrete {𝓙} {𝓖} {J} {Gen} c1 s B X-is-set =
 PC.types-with-decidable-equality-are-♭-discrete Gen c1 𝟚-is-♭-discrete
  (Chart-Index s B) (chart-indices-are-discrete s B X-is-set)
 where
  module PC = gist.RealCohesion.PunctualCohesion fe

\end{code}

The bridge 3.9: local homeomorphisms are ℑ-étale.

\begin{code}

module _ {𝓟 : Universe}
         (pe : propext 𝓤)
         (K : Postulate-K)
         (P : subuniverse (𝓤 ⁺) 𝓟)
         (P-is-reflective : subuniverse-is-reflective P)
         (ν : is-nullification ℑ-generator ℑ-generator-point P)
       where

 private
  P-is-Σ-closed : subuniverse-is-sigma-closed P
  P-is-Σ-closed = nullifications-are-Σ-closed ℑ-generator ℑ-generator-point P ν

  P-is-replete : subuniverse-is-replete P
  P-is-replete = nullifications-are-replete ℑ-generator ℑ-generator-point P ν

 open import gist.Orbifolds.Modalities fe pt P P-is-reflective P-is-Σ-closed
  P-is-replete
  using
   (is-étale ; equivalences-are-étale ; étale-maps-are-closed-under-composition)
 open import gist.Orbifolds.LemmaD fe pt P P-is-reflective P-is-Σ-closed
  P-is-replete
  using (lemma-D)
 open import gist.Orbifolds.LemmasABForIm fe pt 𝓡 {𝓤}
  using (lemma-B-for-carriers-in-𝓤)

 private
  inclusions-of-opens-are-étale
   : {Z : 𝓤 ̇ } (T : Topology Z 𝓤) → is-regular T
   → (C : Subset Z 𝓤) → Topology.is-open T C
   → is-étale (λ (w : Σ z ꞉ Lift (𝓤 ⁺) Z , Lift (𝓤 ⁺) (lower z ∈ C)) → pr₁ w)
  inclusions-of-opens-are-étale T r C oC =
   lemma-B-for-carriers-in-𝓤 pe K P P-is-reflective ν (λ z → Lift (𝓤 ⁺) (z ∈ C))
    (λ z → equiv-to-prop (Lift-≃ (𝓤 ⁺) _) (∈-is-prop z C))
    (λ z z' c d → lift (𝓤 ⁺)
                   (opens-of-regular-spaces-are-infinitesimally-stable T r C oC
                     z z'
                     (lower c) (¬¬-functor _⁻¹ d)))

 source-maps-of-local-homeomorphisms-are-étale
  : {X Y : 𝓤 ̇ } (T : Topology X 𝓤) (T' : Topology Y 𝓤)
  → is-set X → is-set Y
  → is-regular T → is-regular T'
  → has-local-openness T'
  → (B : ℕ → Subset X 𝓤) → is-basis T B
  → (s : X → Y) → is-local-homeomorphism T T' s
  → is-étale (λ (z : Lift (𝓤 ⁺) X) → lift (𝓤 ⁺) (s (lower z)))
 source-maps-of-local-homeomorphisms-are-étale {X} {Y} T T' X-is-set Y-is-set rT
  rT'
                                               local-T' B b s l =
  lemma-D (propositions-are-modal ℑ-generator ℑ-generator-point P ν)
   p s̄ p-is-surjection p-is-étale s̄p-is-étale
  where
   s̄ : Lift (𝓤 ⁺) X → Lift (𝓤 ⁺) Y
   s̄ z = lift (𝓤 ⁺) (s (lower z))

   I : 𝓤 ⁺ ̇
   I = Lift (𝓤 ⁺) (Chart-Index s B)

   I-is-modal : subuniverse-contains P I
   I-is-modal =
    discrete-types-are-ℑ-modal P P-is-reflective ν K I
     (λ i j →
       cases (λ q → inl (ap (lift (𝓤 ⁺)) q)) (λ d → inr (λ q → d (ap lower q)))
               (chart-indices-are-discrete s B X-is-set (lower i) (lower j)))

   C : I → Subset X 𝓤
   C i = chart s B (lower i)

   Xi : I → 𝓤 ⁺ ̇
   Xi i = Σ z ꞉ Lift (𝓤 ⁺) X , Lift (𝓤 ⁺) (lower z ∈ C i)

   p : Σ Xi → Lift (𝓤 ⁺) X
   p w = pr₁ (pr₂ w)

   p-is-étale : is-étale p
   p-is-étale =
    sums-of-étale-maps-are-étale pe K P P-is-reflective ν I I-is-modal Xi
     (λ i w → pr₁ w)
     (λ i → inclusions-of-opens-are-étale T rT (C i)
             (charts-are-open s B T b (lower i)))

   p-is-surjection : is-surjection p
   p-is-surjection z =
    ∥∥-functor (λ (j , m) → (lift (𝓤 ⁺) j , z , lift (𝓤 ⁺) m) , refl)
     (charts-cover s B T (local-homeomorphisms-are-locally-injective s T T' l) b
       (lower z))

   on-a-chart : (i : I) → is-étale (λ (w : Xi i) → s̄ (pr₁ w))
   on-a-chart i =
    ∥∥-rec (being-equiv-is-prop (λ 𝓤 𝓥 → fe {𝓤} {𝓥}) _) γ
     (injective-local-homeomorphisms-are-open-embeddings T T' local-T' Y-is-set
       s l
       (C i) (charts-are-open s B T b (lower i)) (pr₂ (lower i)))
    where
     γ : (Σ V ꞉ Subset Y 𝓤 , Σ m ꞉ ((w : 𝕊 T (C i)) → s (pr₁ w) ∈ V) ,
            Topology.is-open T' V
          × is-homeomorphism (subspace T (C i)) (subspace T' V)
             (corestriction (subspace T (C i)) T' (s ∘ pr₁) V m))
       → is-étale (λ (w : Xi i) → s̄ (pr₁ w))
     γ (V , m , oV , H) =
      étale-maps-are-closed-under-composition c̄ (λ w → pr₁ w)
       (equivalences-are-étale c̄ c̄-is-equiv)
       (inclusions-of-opens-are-étale T' rT' V oV)
      where
       c̄ : Xi i → Σ z ꞉ Lift (𝓤 ⁺) Y , Lift (𝓤 ⁺) (lower z ∈ V)
       c̄ (z , β) =
        lift (𝓤 ⁺) (s (lower z)) , lift (𝓤 ⁺) (m (lower z , lower β))

       c̄-is-equiv : is-equiv c̄
       c̄-is-equiv =
        ∘-is-equiv
         (∘-is-equiv (⌜⌝-is-equiv (≃-sym (stable-subtype-equivalence (_∈ C i))))
                     (pr₁ H))
         (⌜⌝-is-equiv (stable-subtype-equivalence (_∈ V)))

   s̄p-is-étale : is-étale (s̄ ∘ p)
   s̄p-is-étale =
    sums-of-étale-maps-are-étale pe K P P-is-reflective ν I I-is-modal Xi
     (λ i w → s̄ (pr₁ w)) on-a-chart

\end{code}
