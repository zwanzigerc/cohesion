Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026; two sentences updated 13 November 2026,
after the final audits; the proof of discrete-types-are-null shared
with gist.RealCohesion.BooleanTests, 13 November 2026, in the
consolidation that followed. Orbifold gate H3 of Fable's roadmap [1].

Nullification at a family of pointed types
------------------------------------------

The roadmap [1, Section 3.2] assumes, for a family of pointed types
B i, a nullification: a reflective subuniverse whose modal types are
exactly the types null for every B i. For the orbifolds, ℑ is the
nullification at all crisp infinitesimal varieties [1, Section 2].
TypeTopology has no higher inductive types, so the nullification is a
hypothesis (is-nullification below), as in the library's RealNull.

The roadmap also asks the subuniverse to be Σ-closed. That is a
consequence here: a subuniverse whose modal types are the null types
is replete and Σ-closed (nullifications-are-replete,
nullifications-are-Σ-closed). So the interface needs only a
reflective subuniverse and the identification of its modal types.

What is proved. Propositions are modal, because the generators are
pointed (propositions-are-modal); maps from a generator to a modal
type are constant; units of a nullification are surjective (from
Modalities, M1 of the roadmap).

Added at orbifold gate H8, 12 November 2026: the generators are
connected (generators-of-nullifications-are-connected), which is how
the test types of microlinearity become ℑ-connected; and the lemma of
the roadmap's Section 7.1, item 1, stated once: if B has a point and
every map B → 𝟚 is constant, then every type with decidable equality
is B-null (discrete-types-are-null). Its instances are ℝ under R♭ (the
separately proved discrete-types-are-ℝ-null in
gist.RealCohesion.DiscreteSets, gate G15), the crisp infinitesimal
varieties under Postulate K (SmoothLine), and the generators of Axiom
C1.

Reuse. "Null" is is-null of gist.CohesiveApartness.Flat, as the
roadmap asks [1, Section 7.1]; this is why the module needs
--cohesion, although nothing in it is crisp. The library's RealNull
is the case of a single generator: its hypothesis P-is-ℝ-null is the
left side of single-generator-nullification at (ℝ , 0ℝ), and its
maps-from-ℝ-to-modal-types-are-constant is then the instance of
maps-from-generators-to-modal-types-are-constant. The RealNull
statements are single-generator specializations of these general
statements; their proofs remain separate. Replacing them by wrappers
is optional and is not part of the final repairs.

[1] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026, Sections 3.2 and 7.1.
    references/F01-orbifolds-roadmap-rev2.md

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import Modal.Subuniverse

module gist.Orbifolds.Nullification (fe : Fun-Ext) where

open import UF.Base
open import UF.DiscreteAndSeparated using (is-discrete)
open import UF.Equiv
open import UF.EquivalenceExamples using (Π-change-of-variable)
open import UF.Subsingletons

open import gist.CohesiveApartness.Flat
 using (is-null ; null-iff-maps-are-constant)
open import gist.RealCohesion.BooleanTests
 using (maps-into-types-with-decidable-equality-are-constant)

\end{code}

Null types, through their characterization by constant maps: they are
closed under equivalence and under Σ.

\begin{code}

module _ {𝓤 : Universe} (B : 𝓤 ̇ ) (b : B) where

 private
  constant : (A : 𝓤 ̇ ) → 𝓤 ̇
  constant A = (h : B → A) (v : B) → h v ＝ h b

  null-gives-constant : (A : 𝓤 ̇ ) → is-null B A → constant A
  null-gives-constant A = lr-implication (null-iff-maps-are-constant fe B b A)

  constant-gives-null : (A : 𝓤 ̇ ) → constant A → is-null B A
  constant-gives-null A = rl-implication (null-iff-maps-are-constant fe B b A)

 null-types-are-closed-under-equivalence : {A A' : 𝓤 ̇ }
                                         → A' ≃ A
                                         → is-null B A
                                         → is-null B A'
 null-types-are-closed-under-equivalence {A} {A'} φ n =
  constant-gives-null A' γ
  where
   γ : constant A'
   γ h v = h v
           ＝⟨ (inverses-are-retractions ⌜ φ ⌝ ⌜ φ ⌝-is-equiv (h v))⁻¹ ⟩
           ⌜ φ ⌝⁻¹ (⌜ φ ⌝ (h v))
            ＝⟨ ap ⌜ φ ⌝⁻¹ (null-gives-constant A n (⌜ φ ⌝ ∘ h) v) ⟩
           ⌜ φ ⌝⁻¹ (⌜ φ ⌝ (h b))
            ＝⟨ inverses-are-retractions ⌜ φ ⌝ ⌜ φ ⌝-is-equiv (h b) ⟩
           h b                       ∎

 null-types-are-closed-under-Σ : (A : 𝓤 ̇ ) (E : A → 𝓤 ̇ )
                               → is-null B A
                               → ((a : A) → is-null B (E a))
                               → is-null B (Σ E)
 null-types-are-closed-under-Σ A E n m = constant-gives-null (Σ E) γ
  where
   γ : constant (Σ E)
   γ h v = h v                                  ＝⟨ to-Σ-＝ (c' v , refl) ⟩
           (pr₁ (h b) , s v)
            ＝⟨ ap (λ - → pr₁ (h b) , -) (d v) ⟩
           (pr₁ (h b) , s b)                    ＝⟨ ap (λ - → pr₁ (h b) , -) e ⟩
           h b                                  ∎
    where
     c : (v : B) → pr₁ (h v) ＝ pr₁ (h b)
     c = null-gives-constant A n (pr₁ ∘ h)

     c' : (v : B) → pr₁ (h v) ＝ pr₁ (h b)
     c' v = c v ∙ (c b)⁻¹

     s : B → E (pr₁ (h b))
     s v = transport E (c' v) (pr₂ (h v))

     d : (v : B) → s v ＝ s b
     d = null-gives-constant (E (pr₁ (h b))) (m (pr₁ (h b))) s

     e : s b ＝ pr₂ (h b)
     e = ap (λ - → transport E - (pr₂ (h b))) ((right-inverse (c b))⁻¹)

\end{code}

The interface: a subuniverse whose modal types are exactly the types
null for every generator.

\begin{code}

module _ {𝓦 𝓤 𝓥 : Universe}
         {I : 𝓦 ̇ }
         (B : I → 𝓤 ̇ )
         (b : (i : I) → B i)
         (P : subuniverse 𝓤 𝓥)
       where

 is-nullification : 𝓦 ⊔ 𝓤 ⁺ ⊔ 𝓥 ̇
 is-nullification =
  (X : 𝓤 ̇ ) → subuniverse-contains P X ↔ ((i : I) → is-null (B i) X)

 propositions-are-null : (X : 𝓤 ̇ ) → is-prop X → (i : I) → is-null (B i) X
 propositions-are-null X X-is-prop i =
  qinvs-are-equivs (λ x _ → x)
   ((λ h → h (b i)) ,
    (λ x → refl) ,
    (λ h → dfunext fe (λ v → X-is-prop (h (b i)) (h v))))

 module _ (ν : is-nullification) where

  propositions-are-modal : (X : 𝓤 ̇ ) → is-prop X → subuniverse-contains P X
  propositions-are-modal X X-is-prop =
   rl-implication (ν X) (propositions-are-null X X-is-prop)

  maps-from-generators-to-modal-types-are-constant
   : (X : 𝓤 ̇ )
   → subuniverse-contains P X
   → (i : I) (h : B i → X) (v : B i) → h v ＝ h (b i)
  maps-from-generators-to-modal-types-are-constant X m i =
   lr-implication (null-iff-maps-are-constant fe (B i) (b i) X)
    (lr-implication (ν X) m i)

  nullifications-are-replete : subuniverse-is-replete P
  nullifications-are-replete X X' φ m =
   rl-implication (ν X)
    (λ i → null-types-are-closed-under-equivalence (B i) (b i) φ
            (lr-implication (ν X') m i))

  nullifications-are-Σ-closed : subuniverse-is-sigma-closed P
  nullifications-are-Σ-closed A E m n =
   rl-implication (ν (Σ E))
    (λ i → null-types-are-closed-under-Σ (B i) (b i) A E
            (lr-implication (ν A) m i)
            (λ a → lr-implication (ν (E a)) (n a) i))

\end{code}

Types with decidable equality are null at a pointed type all of whose
maps to 𝟚 are constant: a map h into such a type is compared with its
value at the point through the map to 𝟚 that decides the comparison.
That comparison, the local γ of this proof before the consolidation of
13 November 2026, is maps-into-types-with-decidable-equality-are-constant
of gist.RealCohesion.BooleanTests, which gist.RealCohesion.DiscreteSets
and gist.Orbifolds.C1Discreteness use too; the statement keeps its type
and its ordinary function extensionality.

\begin{code}

discrete-types-are-null
 : {𝓤 𝓦 : Universe} (B : 𝓤 ̇ ) (b : B)
 → ((f : B → 𝟚) (v : B) → f v ＝ f b)
 → (X : 𝓦 ̇ ) → is-discrete X → is-null B X
discrete-types-are-null B b c X d =
 rl-implication (null-iff-maps-are-constant fe B b X)
  (maps-into-types-with-decidable-equality-are-constant B b c X d)

\end{code}

Nullness is invariant under equivalence of the generator (added after
the review of 13 November 2026, for the comparison of the generators
of ℑ in MyersMicrolinearity): the constant maps into B → X are the
constant maps into B' → X followed by precomposition with B ≃ B'.

\begin{code}

null-types-are-closed-under-equivalence-of-generators
 : {𝓤 𝓤' 𝓦 : Universe} {B : 𝓤 ̇ } {B' : 𝓤' ̇ }
 → B ≃ B' → (X : 𝓦 ̇ ) → is-null B' X → is-null B X
null-types-are-closed-under-equivalence-of-generators e X n =
 ∘-is-equiv n
  (⌜⌝-is-equiv (Π-change-of-variable fe fe (λ _ → X) ⌜ e ⌝ ⌜ e ⌝-is-equiv))

\end{code}

The case of one generator, the form of the library's RealNull.

\begin{code}

single-generator-nullification
 : {𝓤 𝓥 : Universe} (B₀ : 𝓤 ̇ ) (b₀ : B₀) (P : subuniverse 𝓤 𝓥)
 → ((X : 𝓤 ̇ ) → subuniverse-contains P X ↔ is-null B₀ X)
 ↔ is-nullification (λ (_ : 𝟙 {𝓤₀}) → B₀) (λ _ → b₀) P
single-generator-nullification B₀ b₀ P =
 (λ ν X → (λ m _ → lr-implication (ν X) m) ,
          (λ n → rl-implication (ν X) (n ⋆))) ,
 (λ ν X → (λ m → lr-implication (ν X) m ⋆) ,
          (λ n → rl-implication (ν X) (λ _ → n)))

\end{code}

Units of a nullification are surjective (M1 of the roadmap).

\begin{code}

module _ (pt : propositional-truncations-exist)
         {𝓦 𝓤 𝓥 : Universe}
         {I : 𝓦 ̇ }
         (B : I → 𝓤 ̇ )
         (b : (i : I) → B i)
         (P : subuniverse 𝓤 𝓥)
         (P-is-reflective : subuniverse-is-reflective P)
         (ν : is-nullification B b P)
       where

 open import Modal.ReflectiveSubuniverse P P-is-reflective
  using (η ; ○ ; ○-is-modal ; ○-rec-ext)
 open import UF.ImageAndSurjection pt using (is-surjection)
 open import gist.Orbifolds.Modalities fe pt P P-is-reflective
              (nullifications-are-Σ-closed B b P ν)
              (nullifications-are-replete B b P ν)
  using (units-are-surjective)
 open import gist.RealCohesion.ShapeProducts fe pt P P-is-reflective
              (nullifications-are-Σ-closed B b P ν)
              (nullifications-are-replete B b P ν)
  using (is-○-connected)

 units-of-nullifications-are-surjective : (A : 𝓤 ̇ ) → is-surjection (η A)
 units-of-nullifications-are-surjective =
  units-are-surjective (propositions-are-modal B b P ν)

\end{code}

The generators are connected: the unit of B i is constant, because
maps from a generator to a modal type are, so the identity of ○ (B i)
agrees on units with a constant map.

\begin{code}

 generators-of-nullifications-are-connected : (i : I) → is-○-connected (B i)
 generators-of-nullifications-are-connected i =
  η (B i) (b i) ,
  happly (○-rec-ext (B i) (○ (B i)) (○-is-modal (B i))
           (λ _ → η (B i) (b i)) id
           (dfunext fe (λ v → (maps-from-generators-to-modal-types-are-constant
                                 B b P ν (○ (B i)) (○-is-modal (B i)) i
                                 (η (B i)) v)⁻¹)))

\end{code}
