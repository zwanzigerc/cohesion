Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 October 2026; prose corrected 13 November 2026, after
the final audits; crisp-props-are-♭-discrete made a typed alias of
gist.RealCohesion.PunctualCohesion, 13 November 2026, in the
consolidation that followed. See the AI disclosure in
gist.RealCohesion.index.

Consequences of axiom C1 for crisp sets, and their applications.

 1. Under axiom C1, the counit ♭ B → B is an embedding for every crisp
    set B [1, Theorem 8.21]. Consequently, for a crisp proposition P,
    the set 𝟚-mod P of gist.RealCohesion.OvertConnectedness is
    ♭-discrete. (The module gist.CohesiveApartness.TightApartness
    mentions the first fact but does not formalize it.)

 2. Axiom C1 together with the discrete axiom of choice gives crisp
    excluded middle. This is Diaconescu's argument, applied to the
    crisp ♭-discrete set 𝟚-mod P. Since Shulman derives the discrete
    axiom of choice from his Axiom AC [1, Theorem 6.30], and Axiom R♭
    implies axiom C1, the hypotheses of Shulman's continuity
    conjecture [1, §10.3], namely Axioms R♭ and AC, imply crisp
    excluded middle. It is the internal counterpart of the
    Diaconescu step in Zwanziger's proof that epi-continuity and a
    connected codiscrete classifier force a Boolean base.

 3. Under Axiom R♭, the real line is overtly connected for crisp
    subsets [1, Theorem 11.3], and the approximate intermediate value
    theorem holds for crisp functions [1, Theorem 11.4]. Our proof
    goes through the ♭-discreteness of 𝟚-mod P rather than through
    the shape modality.

 4. Under crisp excluded middle, the analytic Markov principle holds
    for crisp real numbers, and so for real numbers coming from ♭ ℝ.
    (Shulman's Theorem 8.32 needs his Axiom T for arbitrary reals.
    Axiom T doesn't follow from crisp excluded middle, Axiom AC and
    Axiom R♭ [2, Theorem 2.5]. The frame-level part of that
    countermodel is in gist.RealCohesion.PointlessEnd.)

The one ingredient that needs crisp identity induction is that the
constructor of ♭ respects crisp identifications. We take it as the
module parameter crisp-ap-^♭. gist.RealCohesion.Theorems instantiates
it in --safe mode with the proof of
gist.CohesiveApartness.CrispInduction, which derives it from the
native ♯ of Agda 2.9.0; gist.RealCohesion.FlatSplit, which is not
--safe, instantiates it with a proof by pattern matching with
--flat-split, the route for Agda 2.8, kept for comparison. The module
parameters fe, pe, pt and crisp-ap-^♭ are crisp, and so are Axiom C1
and Axiom R♭ where they are assumed, like Shulman's axioms. The
discrete axiom of choice in C1-and-discrete-choice-give-crisp-EM, and
crisp excluded middle in the analytic Markov principle of part 4, are
ordinary arguments.

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3

[2] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, draft of 25 October 2026.
    references/C01-write-up-2026-10-25.tex

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import gist.CohesiveApartness.Flat

module gist.RealCohesion.CrispDiscreteness
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
        (@♭ crisp-ap-^♭ : {@♭ 𝓤 : Universe} {@♭ A : 𝓤 ̇ } {@♭ x y : A}
                        → @♭ x ＝ y → x ^♭ ＝ y ^♭)
       where

open import UF.Base
open import UF.DiscreteAndSeparated using (𝟚-is-discrete)
open import UF.Embeddings
open import UF.Equiv
open import UF.ImageAndSurjection pt
open import UF.LeftCancellable
open import UF.Sets
open import UF.Subsingletons-FunExt
open import UF.SubtypeClassifier
open import gist.RealCohesion.OvertConnectedness fe pe pt
open import gist.RealCohesion.CrispRationals using (module counit-on-crisp-sets)
import gist.RealCohesion.PunctualCohesion fe as PC

open PropositionalTruncation pt

\end{code}

1. Under axiom C1, crisp propositions are ♭-discrete [1, Lemma 8.8],
because every map from a pointed type into a proposition is constant
(since the consolidation of 13 November 2026, a typed alias of the
statement of gist.RealCohesion.PunctualCohesion, which takes the family
and C1 as ordinary hypotheses, to which this module passes its crisp
ones).
Hence the counit is left cancellable, and so an embedding, on crisp
sets [1, Theorem 8.21]: given crisp x and y with x ＝ y, the crisp
proposition x ＝ y is ♭-discrete, so the identification may be taken
crisp, and then crisp-ap-^♭ applies.

\begin{code}

module _ {@♭ 𝓥 𝓦 : Universe}
         {@♭ J : 𝓥 ̇ }
         (@♭ R : J → 𝓦 ̇ )
         (@♭ c1 : Axiom-C1 R)
       where

 open Axiom-C1 c1

 crisp-props-are-♭-discrete
  : {@♭ 𝓣 : Universe} (@♭ P : 𝓣 ̇ ) → @♭ is-prop P → is-♭-discrete P
 crisp-props-are-♭-discrete P i = PC.crisp-propositions-are-♭-discrete R c1 P i

 open counit-on-crisp-sets crisp-ap-^♭ crisp-props-are-♭-discrete public

\end{code}

For a crisp proposition P, the counit of 𝟚-mod P is moreover
surjective, because the two points [ ₀ ] and [ ₁ ] are crisp. So
𝟚-mod P is ♭-discrete. This is a special case of [1, Lemma 8.24],
whose proof uses the closure of discrete types under set quotients,
which we avoid.

\begin{code}

 𝟚-mod-is-♭-discrete : {@♭ 𝓣 : Universe} (@♭ P : Ω 𝓣)
                     → is-♭-discrete (𝟚-mod P)
 𝟚-mod-is-♭-discrete P =
  surjective-embeddings-are-equivs ♭-counit
   (♭-counit-is-embedding-on-crisp-sets (𝟚-mod P) (𝟚-mod-is-set P))
   σ
  where
   σ : is-surjection (♭-counit {_} {𝟚-mod P})
   σ y = ∥∥-functor γ (𝟚-mod-induction P y)
    where
     γ : (y ＝ [ ₀ ]) + (y ＝ [ ₁ ]) → Σ u ꞉ ♭ (𝟚-mod P) , ♭-counit u ＝ y
     γ (inl e) = ([ ₀ ] ^♭) , (e ⁻¹)
     γ (inr e) = ([ ₁ ] ^♭) , (e ⁻¹)

\end{code}

2. The discrete axiom of choice [1, Theorem 6.30]: for a crisply
♭-discrete crisp set A and a crisp family P over A that is crisply
pointwise inhabited, the product of P is inhabited. Shulman derives
this from his Axiom AC.

\begin{code}

Discrete-Choice : (@♭ 𝓤 𝓥 : Universe) → (𝓤 ⊔ 𝓥) ⁺ ̇
Discrete-Choice 𝓤 𝓥 =
   (@♭ A : 𝓤 ̇ )
 → @♭ is-♭-discrete A
 → @♭ is-set A
 → (@♭ P : A → 𝓥 ̇ )
 → @♭ ((x : A) → ∥ P x ∥)
 → ∥ ((x : A) → P x) ∥

\end{code}

Diaconescu's argument. Given a crisp proposition P, the quotient map
𝟚 → 𝟚-mod P is crisp and surjective, and 𝟚-mod P is a crisp ♭-discrete
set, so it merely has a section s. Comparing the two values of s,
which is possible because 𝟚 has decidable equality, decides P.

\begin{code}

decide-from-section : {𝓤 : Universe} (P : Ω 𝓤)
                    → ((y : 𝟚-mod P) → Σ j ꞉ 𝟚 , [ j ] ＝ y)
                    → P holds + ¬ (P holds)
decide-from-section P s = δ (𝟚-is-discrete (σ [ ₀ ]) (σ [ ₁ ]))
 where
  σ : 𝟚-mod P → 𝟚
  σ y = pr₁ (s y)

  ρ : (y : 𝟚-mod P) → [ σ y ] ＝ y
  ρ y = pr₂ (s y)

  δ : is-decidable (σ [ ₀ ] ＝ σ [ ₁ ]) → P holds + ¬ (P holds)
  δ (inl e) = inl (lr-implication (points-of-𝟚-mod-are-equal-iff P)
                    ([ ₀ ]         ＝⟨ ρ [ ₀ ] ⁻¹ ⟩
                     [ σ [ ₀ ] ]   ＝⟨ ap [_] e ⟩
                     [ σ [ ₁ ] ]   ＝⟨ ρ [ ₁ ] ⟩
                     [ ₁ ]         ∎))
  δ (inr ν) = inr (λ p → ν (ap σ (rl-implication
                                   (points-of-𝟚-mod-are-equal-iff P) p)))

module _ {@♭ 𝓥 𝓦 : Universe}
         {@♭ J : 𝓥 ̇ }
         (@♭ R : J → 𝓦 ̇ )
         (@♭ c1 : Axiom-C1 R)
       where

 C1-and-discrete-choice-give-crisp-EM
  : {@♭ 𝓤 : Universe}
  → Discrete-Choice (𝓤 ⁺) (𝓤 ⁺)
  → Crisp-EM 𝓤
 C1-and-discrete-choice-give-crisp-EM {𝓤} dc P i =
  ∥∥-rec (decidability-of-prop-is-prop fe i) (decide-from-section (P , i))
   (dc (𝟚-mod (P , i))
       (𝟚-mod-is-♭-discrete R c1 (P , i))
       (𝟚-mod-is-set (P , i))
       (λ y → Σ j ꞉ 𝟚 , [ j ] ＝ y)
       (corestrictions-are-surjections (χ (P , i))))

\end{code}

3. Axiom R♭, in the form of singly generated punctual cohesion with
the real line as generator, pointed by 0 (see
gist.CohesiveApartness.Flat). For crisp subsets U and V, the
proposition that they meet is crisp, so 𝟚-mod of it is ♭-discrete,
hence ℝ-null by Axiom R♭, and gist.RealCohesion.OvertConnectedness
gives that U and V meet.

\begin{code}

open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import Notation.Order

module _ (@♭ r♭ : Singly-Generated-Punctual-Cohesion ℝ 0ℝ) where

 private
  c1 : Axiom-C1 (λ (_ : 𝟙 {𝓤₀}) → ℝ)
  c1 = singly-generated-punctual-cohesion-gives-Axiom-C1 fe ℝ 0ℝ r♭

 crisp-𝟚-mod-is-ℝ-null : (@♭ P : Ω 𝓤₁) → is-null ℝ (𝟚-mod P)
 crisp-𝟚-mod-is-ℝ-null P =
  rl-implication (null-iff-maps-are-constant fe ℝ 0ℝ (𝟚-mod P))
   (lr-implication (r♭ (𝟚-mod P))
     (𝟚-mod-is-♭-discrete (λ (_ : 𝟙 {𝓤₀}) → ℝ) c1 P))

 crisp-overt-connectedness-of-ℝ
  : (@♭ U V : ℝ → Ω 𝓤₁)
  → ((x : ℝ) → U x holds ∨ V x holds)
  → (∃ x ꞉ ℝ , U x holds)
  → (∃ x ꞉ ℝ , V x holds)
  → ∃ x ꞉ ℝ , U x holds × V x holds
 crisp-overt-connectedness-of-ℝ U V cover =
  meet-from-nullness {𝓤₀} {𝓤₁} U V cover
   (crisp-𝟚-mod-is-ℝ-null (meet {𝓤₀} {𝓤₁} U V))

 crisp-approximate-IVT
  : (@♭ f : ℝ → ℝ) (@♭ p q : ℝ) (a b : ℝ)
  → p < q
  → f a < q
  → p < f b
  → ∃ x ꞉ ℝ , (p < f x) × (f x < q)
 crisp-approximate-IVT f p q a b p<q fa<q p<fb =
  approximate-root-from-meet f p q
   (crisp-overt-connectedness-of-ℝ (below f q) (above f p)
     (below-above-cover f p q p<q)
     ∣ a , lift 𝓤₁ fa<q ∣
     ∣ b , lift 𝓤₁ p<fb ∣)
  where
   open import UF.UniverseEmbedding

\end{code}

4. The analytic Markov principle for crisp reals, from crisp excluded
middle and the tightness of the apartness of real numbers. For a
crisp real number the statement x ♯ y is a crisp proposition, so it is
decided by crisp excluded middle, and its failure would make x and y
equal.

\begin{code}

crisp-analytic-Markov : Crisp-EM 𝓤₀
                      → (@♭ x y : ℝ) → ¬ (x ＝ y) → x ♯ y
crisp-analytic-Markov cem x y ν = γ (cem (x ♯ y) ∨-is-prop)
 where
  γ : is-decidable (x ♯ y) → x ♯ y
  γ (inl a) = a
  γ (inr na) = 𝟘-elim (ν (♯-is-tight x y na))

analytic-Markov-on-♭ℝ : Crisp-EM 𝓤₀
                      → (u v : ♭ ℝ)
                      → ¬ (♭-counit u ＝ ♭-counit v)
                      → ♭-counit u ♯ ♭-counit v
analytic-Markov-on-♭ℝ cem (x ^♭) (y ^♭) = crisp-analytic-Markov cem x y

\end{code}
