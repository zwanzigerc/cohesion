Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 13 November 2026 (local time); the type of
theorem-T5b-literal displayed in full on the same day, after the final
audits [5]; the forms for set-indexed covers added later that day, in
the third part of the consolidation [6]. Orbifold gate H10 of Fable's
roadmap [1, Section 3.10]: the target T5b.

T5b: Dubuc–Penon properness implies the replacement hypotheses
--------------------------------------------------------------

The target T5b [1, Section 3.10; 2; 3, Section 4]: let G be a crisp
pregroupoid whose objects G₀ and arrows G₁ form ordinary manifolds, with
a crisp basis of the arrows, and whose source map is ℑ-étale. If the
anchor a = (s , t) is Dubuc–Penon proper, then

  (i)   G₀ and G₁ have open singletons and decidable equality, at every
        ordinary point;
  (ii)  s is an ordinary local homeomorphism (the genuine predicate);
  (iii) a is cover-proper (the official condition of CoverProperness).

  theorem-T5b : all three, for the Dubuc–Penon properness of the module
  DubucPenon at the universe 𝓤 of the carriers, the predicate of T5a
  (where 𝓤 = 𝓤₀);

  theorem-T5b-literal : the same with ℑ the nullification at Myers's
  infinitesimal varieties in the adopted, presentation-based reading of
  MyersMicrolinearity, converted by
  literal-nullifications-are-nullifications; its hypotheses and its
  type are displayed in full, as in Fable's scratch check
  T5bLiteralSignatureCheck [5, Section 7, B6]. For the reading of
  "literal" and of ℑ, see gist.Orbifolds.index, the paragraph on the
  scope of the statements;

  anchor-is-cover-proper-for-set-indices, theorem-T5b-for-set-indices,
  theorem-T5b-literal-for-set-indices : the same with (iii) for
  set-indexed covers, the condition of the memo (CoverProperness), by
  restriction; the older forms are unchanged.

Proof [2, Sections 2–5; 4]. The orbit relation is decidable, a crisp
decision family comes from C1, and the orbit set, objects and arrows are
ℑ-modal (OrbitSets). An ℑ-modal ordinary manifold has open singletons
and decidable equality (ZeroDimensionalCharts): this is (i). The
singleton {g} is open, so is {s g}, every subset of a singleton subspace
is open, and a map between singletons is an equivalence: this gives
(ii) with continuity in both directions. For (iii), let (V_i) be a crisp
cover of G₁ by opens, with a crisp ♭-discrete index type, and b an
ordinary point of G₀ × G₀. That product has decidable equality, so it is
♭-discrete (C1Discreteness) and b may be taken crisp, inside the
proposition to be proved. The fibre of a over a crisp b is a crisp
subset of G₁, Dubuc–Penon compact by properness, so it has a finite
subcover, a finite indexed list of members of the cover in which
repetitions are allowed (FiniteSubcovers: Theorem 6.2.13 with the
Covering Property,
crisp excluded middle for the crisp refinement predicate, finite
choice). The open neighbourhood is W = {b} = {x} × {y}, whose whole
preimage is that fibre.

Inventory: Postulates K, O, Exp (for the translation law) and E; J for
the dual numbers (its injectivity half); ℑ as the nullification of core
item 4, with the preservation of crisp pullbacks (for Corollary F′);
Axiom C1, for an arbitrary family of pointed generators; crisp excluded
middle at 𝓤.

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026.
    references/F01-orbifolds-roadmap-rev2.md
[2] GPT-6 Astra. DP properness implies the replacement over the
    five-item core, 11 November 2026.
    references/A02-dp-properness-implies-replacement.txt
[3] GPT-6 Astra. Original targets, 12 November 2026
    (references/A31-original-targets.txt).
[4] GPT-6 Astra. H10 T5b implementation preflight, 13 November 2026
    (UTC).
    references/A24-t5b-preflight.txt
[5] Claude Fable 5.2. Final audit: the Shulman / real-cohesion
    formalization and the Orbifolds targets T1–T5b, 13 November 2026.
    references/F09-final-audit.md
[6] GPT-6 Astra. Consolidation implementation, third release
    (OPUS-CONSOLIDATION-RELEASE-03), 13 November 2026, with the review
    COVER-INDEX-PLAN-REVIEW of the same day, and Claude Fable 5.2's
    plan of 13 November 2026
    (references/F20-cover-index-plan.md, SHA-256
    10fb9683…). The additions are those of its scratch check
    ProperEtaleGroupoidsSetIndexCheck.lagda (SHA-256 58d7c45a…).
    references/A33-consolidation-release-03.txt
    references/A34-cover-index-plan-review.txt

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import Modal.Subuniverse
open import gist.Orbifolds.SmoothLine
 using (Commutative-Ring ; module smooth-line)

module gist.Orbifolds.ProperEtaleGroupoids
        (@♭ fe : Fun-Ext)
        (@♭ pt : propositional-truncations-exist)
        (@♭ 𝓡 : Commutative-Ring)
        {@♭ 𝓤 : Universe}
       where

open import Fin.Type
open import TypeTopology.SigmaDiscrete using (×-is-discrete)
open import UF.Base
open import UF.DiscreteAndSeparated using (is-discrete)
open import UF.Equiv
open import UF.Sets
open import UF.SubtypeClassifier
open import UF.UniverseEmbedding using (Lift ; lift ; lower)
open import gist.CohesiveApartness.Flat
 using (♭ ; _^♭ ; ♭-counit ; is-♭-discrete ; Axiom-C1 ; Crisp-EM)
open import gist.Orbifolds.SmoothOrder
open import gist.Orbifolds.Manifolds
open import gist.Orbifolds.CoveringProperty

open PropositionalTruncation pt
open smooth-line fe pt 𝓡
open smooth-order fe pt 𝓡
open ordinary-manifolds fe pt 𝓡
open covering-property fe pt 𝓡 using (Postulate-E)
open import gist.Orbifolds.Topology fe pt
open import gist.Orbifolds.RezkCompletion fe pt {𝓤} {𝓤}
open import gist.Orbifolds.CoverFiniteness fe pt using (anchor)
open import gist.Orbifolds.CoverProperness fe pt
open import gist.Orbifolds.DubucPenon fe pt
open import gist.Orbifolds.C1Discreteness fe
open import gist.Orbifolds.FiniteSubcovers fe pt 𝓡
 using (crisp-DP-compact-subsets-have-finite-subcovers)
open import gist.Orbifolds.SmoothLineGroupoid fe pt 𝓡
 using (Postulate-J-for-dual-numbers)
open import gist.Orbifolds.Microlinearity fe pt 𝓡 {𝓤 ⁺}
 using (ℑ-generator ; ℑ-generator-point)
open import gist.Orbifolds.MyersMicrolinearity fe pt 𝓡 {𝓤 ⁺}
 using (literal-ℑ-generator ; literal-ℑ-generator-point ;
         literal-nullifications-are-nullifications)
open import gist.Orbifolds.Nullification fe using (is-nullification)
open import gist.Orbifolds.OrbitSets fe pt 𝓡 {𝓤}
open import gist.Orbifolds.ZeroDimensionalCharts fe pt 𝓡 {𝓤}

\end{code}

Every subset of a singleton subspace is open.

\begin{code}

module _ {X : 𝓤 ̇ } (X-is-set : is-set X) (T : Topology X 𝓤) where

 point : X → Subset X 𝓤
 point p y = (y ＝ p) , X-is-set

 subsets-of-singleton-subspaces-are-open
  : (p : X) → Topology.is-open T (point p)
  → (W : Subset (𝕊 T (point p)) 𝓤) → Topology.is-open (subspace T (point p)) W
 subsets-of-singleton-subspaces-are-open p o W w m =
  ∣ point p , o , pr₂ w ,
    (λ w' _ → transport (_∈ W)
               (to-subtype-＝ (λ y → X-is-set) (pr₂ w ∙ (pr₂ w')⁻¹)) m) ∣

 maps-from-singleton-subspaces-are-continuous
  : (p : X) → Topology.is-open T (point p)
  → {𝓨 : Universe} {Y : 𝓨 ̇ } (T' : Topology Y 𝓤) (f : 𝕊 T (point p) → Y)
  → is-continuous (subspace T (point p)) T' f
 maps-from-singleton-subspaces-are-continuous p o T' f V' _ =
  subsets-of-singleton-subspaces-are-open p o (λ w → V' (f w))

\end{code}

T5b.

\begin{code}

module _ (K : Postulate-K)
         (O : Postulate-O)
         (Exp : Postulate-Exp O)
         (J : Postulate-J-for-dual-numbers)
         {𝓟 : Universe}
         (P : subuniverse (𝓤 ⁺) 𝓟)
         (P-is-reflective : subuniverse-is-reflective P)
         (ν : is-nullification ℑ-generator ℑ-generator-point P)
       where

 private
  translation : Translation-Law O
  translation = translation-law-from-Exp O Exp

 module _ (@♭ cem : Crisp-EM 𝓤)
          (E : Postulate-E O Exp K 𝓤)
          (π : ○-preserves-crisp-pullbacks K P P-is-reflective ν)
          {𝓙 𝓖 : Universe} {Jg : 𝓙 ̇ } {Gen : Jg → 𝓖 ̇ } (c1 : Axiom-C1 Gen)
          (@♭ G : Pregroupoid)
          {n₀ : ℕ}
           (𝓜₀ : Ordinary-Manifold O translation K n₀ (Pregroupoid.ob G))
          {n₁ : ℕ} (T₁ : Topology (arrows G) 𝓤)
           (@♭ B₁ : ℕ → Subset (arrows G) 𝓤)
          (L₁ : Ordinary-Manifold-Laws O translation K n₁ T₁ B₁)
          (s-is-étale : is-étale K P P-is-reflective ν
                         (λ (z : Lift (𝓤 ⁺) (arrows G)) →
                           lift (𝓤 ⁺) (source G (lower z))))
          (a-is-DP-proper : is-DP-proper (anchor G))
        where

  private
   T₀ : Topology (Pregroupoid.ob G) 𝓤
   T₀ = Ordinary-Manifold.topology 𝓜₀

   ob-is-set : is-set (Pregroupoid.ob G)
   ob-is-set = Ordinary-Manifold.carrier-is-set 𝓜₀

   𝓜₁ : Ordinary-Manifold O translation K n₁ (arrows G)
   𝓜₁ = manifold-from-laws O translation K T₁ B₁ L₁

   arrows-are-set : is-set (arrows G)
   arrows-are-set = Ordinary-Manifold-Laws.carrier-is-set L₁

   d : Orbit-Decider G
   d = orbit-relations-are-decidable G ob-is-set a-is-DP-proper

   modalities : ♭ (Orbit-Decider G)
              → is-ℑ-modal K P P-is-reflective ν (Pregroupoid.ob G)
              × is-ℑ-modal K P P-is-reflective ν (arrows G)
   modalities (d₀ ^♭) =
    objects-are-modal K P P-is-reflective ν π c1 G ob-is-set s-is-étale d₀ ,
    arrows-are-modal K P P-is-reflective ν π c1 G ob-is-set s-is-étale d₀

   objects-are-modal' = pr₁ (modalities (crisp-orbit-deciders c1 G d))
   arrows-are-modal' = pr₂ (modalities (crisp-orbit-deciders c1 G d))

\end{code}

(i) Open singletons and decidable equality.

\begin{code}

  objects-have-open-singletons
   : (x : Pregroupoid.ob G) → Topology.is-open T₀ (point ob-is-set T₀ x)
  objects-have-open-singletons =
   modal-manifolds-have-open-singletons O Exp K J P P-is-reflective ν 𝓜₀
    objects-are-modal'

  objects-have-decidable-equality : is-discrete (Pregroupoid.ob G)
  objects-have-decidable-equality =
   modal-manifolds-have-decidable-equality O Exp K J P P-is-reflective ν 𝓜₀
    objects-are-modal'

  arrows-have-open-singletons
   : (a : arrows G) → Topology.is-open T₁ (point arrows-are-set T₁ a)
  arrows-have-open-singletons =
   modal-manifolds-have-open-singletons O Exp K J P P-is-reflective ν 𝓜₁
    arrows-are-modal'

  arrows-have-decidable-equality : is-discrete (arrows G)
  arrows-have-decidable-equality =
   modal-manifolds-have-decidable-equality O Exp K J P P-is-reflective ν 𝓜₁
    arrows-are-modal'

\end{code}

(ii) The source map is a local homeomorphism.

\begin{code}

  source-is-a-local-homeomorphism : is-local-homeomorphism T₁ T₀ (source G)
  source-is-a-local-homeomorphism a =
   ∣ U , V , m , arrows-have-open-singletons a ,
    objects-have-open-singletons (source G a) ,
     refl , refl , e , c , c' ∣
   where
    U = point arrows-are-set T₁ a
    V = point ob-is-set T₀ (source G a)

    m : (u : arrows G) → u ∈ U → source G u ∈ V
    m u p = ap (source G) p

    f = restriction T₁ T₀ (source G) U V m

    e : is-equiv f
    e = maps-of-singletons-are-equivs f
         (singleton-types'-are-singletons a)
          (singleton-types'-are-singletons (source G a))

    c : is-continuous (subspace T₁ U) (subspace T₀ V) f
    c = maps-from-singleton-subspaces-are-continuous arrows-are-set T₁ a
         (arrows-have-open-singletons a) (subspace T₀ V) f

    c' : is-continuous (subspace T₀ V) (subspace T₁ U) (inverse f e)
    c' = maps-from-singleton-subspaces-are-continuous ob-is-set T₀ (source G a)
          (objects-have-open-singletons (source G a)) (subspace T₁ U)
           (inverse f e)

\end{code}

(iii) The anchor is cover-proper.

\begin{code}

  private
   base-is-set : is-set (Pregroupoid.ob G × Pregroupoid.ob G)
   base-is-set = ×-is-set ob-is-set ob-is-set

   base-is-♭-discrete : is-♭-discrete (Pregroupoid.ob G × Pregroupoid.ob G)
   base-is-♭-discrete =
    types-with-decidable-equality-are-♭-discrete c1
     (Pregroupoid.ob G × Pregroupoid.ob G)
     (×-is-discrete objects-have-decidable-equality
       objects-have-decidable-equality)

  anchor-is-cover-proper : is-cover-proper T₁ (product T₀ T₀) (anchor G)
  anchor-is-cover-proper I V δ o c b =
   transport Goal (inverses-are-sections ♭-counit base-is-♭-discrete b)
    (at-crisp-points (inverse ♭-counit base-is-♭-discrete b))
   where
    Goal : Pregroupoid.ob G × Pregroupoid.ob G → 𝓤 ⁺ ̇
    Goal b' = ∃ W ꞉ Subset (Pregroupoid.ob G × Pregroupoid.ob G) 𝓤 ,
                Topology.is-open (product T₀ T₀) W × b' ∈ W
              × (Σ n ꞉ ℕ , Σ F ꞉ (Fin n → I) ,
                   ((e : arrows G) → anchor G e ∈ W
                    → ∃ j ꞉ Fin n , e ∈ V (F j)))

    at-crisp-points : (u : ♭ (Pregroupoid.ob G × Pregroupoid.ob G))
                    → Goal (♭-counit u)
    at-crisp-points (b' ^♭) =
     ∥∥-functor
      (λ (n , F , cov) →
        W , W-is-open , refl , n , F , (λ e (q : anchor G e ＝ b') → cov e q))
      (crisp-DP-compact-subsets-have-finite-subcovers O Exp K E cem T₁
        (Ordinary-Manifold-Laws.topology-is-regular L₁) B₁
        (Ordinary-Manifold-Laws.basis-is-basis L₁)
        (λ e → anchor G e ＝ b') (λ e → base-is-set)
        (DP-proper-maps-have-DP-compact-fibres (anchor G) base-is-set
          a-is-DP-proper b')
        I V o (λ e _ → c e))
     where
      W : Subset (Pregroupoid.ob G × Pregroupoid.ob G) 𝓤
      W z = (z ＝ b') , base-is-set

      W-is-open : Topology.is-open (product T₀ T₀) W
      W-is-open z q =
       ∣ point ob-is-set T₀ (pr₁ b') , point ob-is-set T₀ (pr₂ b') ,
         objects-have-open-singletons (pr₁ b') ,
          objects-have-open-singletons (pr₂ b') ,
         ap pr₁ q , ap pr₂ q ,
         (λ x y (p : x ＝ pr₁ b') (p' : y ＝ pr₂ b') → ap₂ _,_ p p') ∣

\end{code}

The theorem.

\begin{code}

  theorem-T5b
   : (((x : Pregroupoid.ob G) → Topology.is-open T₀ (point ob-is-set T₀ x))
       × is-discrete (Pregroupoid.ob G))
   × (((a : arrows G) → Topology.is-open T₁ (point arrows-are-set T₁ a))
       × is-discrete (arrows G))
   × is-local-homeomorphism T₁ T₀ (source G)
   × is-cover-proper T₁ (product T₀ T₀) (anchor G)
  theorem-T5b =
   (objects-have-open-singletons , objects-have-decidable-equality) ,
   (arrows-have-open-singletons , arrows-have-decidable-equality) ,
   source-is-a-local-homeomorphism ,
   anchor-is-cover-proper

  anchor-is-cover-proper-for-set-indices
   : is-cover-proper-for-set-indices T₁ (product T₀ T₀) (anchor G)
  anchor-is-cover-proper-for-set-indices =
   cover-proper-maps-are-cover-proper-for-set-indices T₁ (product T₀ T₀)
    (anchor G) anchor-is-cover-proper

  theorem-T5b-for-set-indices
   : (((x : Pregroupoid.ob G) → Topology.is-open T₀ (point ob-is-set T₀ x))
       × is-discrete (Pregroupoid.ob G))
   × (((a : arrows G) → Topology.is-open T₁ (point arrows-are-set T₁ a))
       × is-discrete (arrows G))
   × is-local-homeomorphism T₁ T₀ (source G)
   × is-cover-proper-for-set-indices T₁ (product T₀ T₀) (anchor G)
  theorem-T5b-for-set-indices =
   (objects-have-open-singletons , objects-have-decidable-equality) ,
   (arrows-have-open-singletons , arrows-have-decidable-equality) ,
   source-is-a-local-homeomorphism ,
   anchor-is-cover-proper-for-set-indices

\end{code}

T5b for the nullification at Myers's infinitesimal varieties in the
adopted reading of MyersMicrolinearity, with the same hypotheses as
theorem-T5b, written out, and the same conclusions. The proof is
theorem-T5b, with the nullification at the spectra of crisp
presentations obtained from ν by
literal-nullifications-are-nullifications.

\begin{code}

module _ (K : Postulate-K)
         (O : Postulate-O)
         (Exp : Postulate-Exp O)
         (J : Postulate-J-for-dual-numbers)
         {𝓟 : Universe}
         (P : subuniverse (𝓤 ⁺) 𝓟)
         (P-is-reflective : subuniverse-is-reflective P)
         (ν : is-nullification literal-ℑ-generator literal-ℑ-generator-point P)
       where

 private
  ν' : is-nullification ℑ-generator ℑ-generator-point P
  ν' = lr-implication (literal-nullifications-are-nullifications P) ν

  translation : Translation-Law O
  translation = translation-law-from-Exp O Exp

 module _ (@♭ cem : Crisp-EM 𝓤)
          (E : Postulate-E O Exp K 𝓤)
          (π : ○-preserves-crisp-pullbacks K P P-is-reflective ν')
          {𝓙 𝓖 : Universe} {Jg : 𝓙 ̇ } {Gen : Jg → 𝓖 ̇ } (c1 : Axiom-C1 Gen)
          (@♭ G : Pregroupoid)
          {n₀ : ℕ}
           (𝓜₀ : Ordinary-Manifold O translation K n₀ (Pregroupoid.ob G))
          {n₁ : ℕ} (T₁ : Topology (arrows G) 𝓤)
           (@♭ B₁ : ℕ → Subset (arrows G) 𝓤)
          (L₁ : Ordinary-Manifold-Laws O translation K n₁ T₁ B₁)
          (s-is-étale : is-étale K P P-is-reflective ν'
                         (λ (z : Lift (𝓤 ⁺) (arrows G)) →
                           lift (𝓤 ⁺) (source G (lower z))))
          (a-is-DP-proper : is-DP-proper (anchor G))
        where

  private
   T₀ : Topology (Pregroupoid.ob G) 𝓤
   T₀ = Ordinary-Manifold.topology 𝓜₀

   ob-is-set : is-set (Pregroupoid.ob G)
   ob-is-set = Ordinary-Manifold.carrier-is-set 𝓜₀

   arrows-are-set : is-set (arrows G)
   arrows-are-set = Ordinary-Manifold-Laws.carrier-is-set L₁

  theorem-T5b-literal
   : (((x : Pregroupoid.ob G) → Topology.is-open T₀ (point ob-is-set T₀ x))
       × is-discrete (Pregroupoid.ob G))
   × (((a : arrows G) → Topology.is-open T₁ (point arrows-are-set T₁ a))
       × is-discrete (arrows G))
   × is-local-homeomorphism T₁ T₀ (source G)
   × is-cover-proper T₁ (product T₀ T₀) (anchor G)
  theorem-T5b-literal =
   theorem-T5b K O Exp J P P-is-reflective ν' cem E π c1 G 𝓜₀ T₁ B₁ L₁
    s-is-étale a-is-DP-proper

  theorem-T5b-literal-for-set-indices
   : (((x : Pregroupoid.ob G) → Topology.is-open T₀ (point ob-is-set T₀ x))
       × is-discrete (Pregroupoid.ob G))
   × (((a : arrows G) → Topology.is-open T₁ (point arrows-are-set T₁ a))
       × is-discrete (arrows G))
   × is-local-homeomorphism T₁ T₀ (source G)
   × is-cover-proper-for-set-indices T₁ (product T₀ T₀) (anchor G)
  theorem-T5b-literal-for-set-indices =
   theorem-T5b-for-set-indices K O Exp J P P-is-reflective ν' cem E π c1 G 𝓜₀
    T₁ B₁ L₁ s-is-étale a-is-DP-proper

\end{code}

