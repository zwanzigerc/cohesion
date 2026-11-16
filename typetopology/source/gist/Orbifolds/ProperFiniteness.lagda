Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. Orbifold gate H1 of Fable's roadmap [2].

Proper finiteness
-----------------

Myers [1, Definition 6.1.3, first sentence] calls a type properly
finite if it has decidable equality and is subfinitely enumerable:
there are a natural number n, a subtype S of Fin n and a surjection
S ↠ X. The second sentence of that definition, and parts 5 and 6 of
his Proposition 6.1.9, rest on the unrestricted direction of Shulman's
Lemma 8.15, which is false; they are not used anywhere in this folder
[2, Section 3.1].

Formal reading. A subtype of Fin n is represented by a type S in the
universe of X together with an embedding S ↪ Fin n. The lemma
subfinite-enumerations-agree below shows that this is the same as a
proposition-valued predicate on Fin n with a surjection from its total
type, which is the literal reading of "a subtype S of Fin n". The
enumeration merely exists (it is truncated), so being properly finite
is a property (being-properly-finite-is-prop).

The closure facts are those of GPT-6 Astra's note [3, Section 1]:

  1a  a type that embeds into some Fin n is properly finite;
  1b  subtypes of properly finite types are properly finite;
  1c  binary products of properly finite types are properly finite.

They are the parts of Myers's 6.1.5 and 6.1.9(1),(2) that the targets
need, proved directly as in [3]. Closure under equivalence, and the
form of 1b and 1c used for identity types of pullbacks (a subtype of
a product), are added for the next gate. Closure under equivalence
into a larger universe was added at orbifold gate H7, on 12 November
2026, for the identity types of Rezk completions; finite types (merely
equivalent to some Fin n, TypeTopology's finite-linear-order) were
added at gate H8, for finite groups.

[1] D. J. Myers. Orbifolds as microlinear types in synthetic
    differential cohesive homotopy type theory. arXiv:2205.15887v1.
[2] Claude Fable 5.2. Roadmap for Opus: the Myers thread in Agda,
    revision 2, 12 November 2026, Section 3.1.
    references/F01-orbifolds-roadmap-rev2.md
[3] GPT-6 Astra. All of Myers Section 6.4 over the adopted five-item
    core, 11 November 2026, Section 1.
    references/A01-section-6-4-over-the-core.txt

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc

module gist.Orbifolds.ProperFiniteness
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
       where

open PropositionalTruncation pt

open import Fin.ArithmeticViaEquivalence using (×construction)
open import Fin.Bishop using (finite-linear-order)
open import Fin.Topology using (Fin-is-discrete)
open import Fin.Type
open import TypeTopology.SigmaDiscrete using (×-is-discrete)
open import UF.DiscreteAndSeparated
open import UF.Embeddings
open import UF.Equiv
open import UF.EquivalenceExamples
open import UF.ImageAndSurjection pt
open import UF.PairFun
open import UF.Sets
open import UF.Subsingletons
open import UF.SubtypeClassifier
open import UF.UniverseEmbedding using (Lift ; Lift-≃)

\end{code}

The definitions.

\begin{code}

subfinite-enumeration : 𝓤 ̇ → 𝓤 ⁺ ̇
subfinite-enumeration {𝓤} X = Σ n ꞉ ℕ , Σ S ꞉ 𝓤 ̇ , (S ↪ Fin n) × (S ↠ X)

is-subfinitely-enumerable : 𝓤 ̇ → 𝓤 ⁺ ̇
is-subfinitely-enumerable X = ∥ subfinite-enumeration X ∥

is-properly-finite : 𝓤 ̇ → 𝓤 ⁺ ̇
is-properly-finite X = is-discrete X × is-subfinitely-enumerable X

being-properly-finite-is-prop : {X : 𝓤 ̇ } → is-prop (is-properly-finite X)
being-properly-finite-is-prop = ×-is-prop
                                 (being-discrete-is-prop (λ 𝓤 𝓥 → fe))
                                 ∥∥-is-prop

properly-finite-types-are-sets : {X : 𝓤 ̇ } → is-properly-finite X → is-set X
properly-finite-types-are-sets (d , _) = discrete-types-are-sets d

\end{code}

The literal reading: a subtype of Fin n as a proposition-valued
predicate.

\begin{code}

subtype-enumeration : 𝓤 ̇ → 𝓤 ⁺ ̇
subtype-enumeration {𝓤} X =
 Σ n ꞉ ℕ , Σ A ꞉ (Fin n → Ω 𝓤) , (Σ i ꞉ Fin n , A i holds) ↠ X

subfinite-enumerations-agree
 : {X : 𝓤 ̇ }
 → (subfinite-enumeration X → subtype-enumeration X)
 × (subtype-enumeration X → subfinite-enumeration X)
subfinite-enumerations-agree {𝓤} {X} = f , g
 where
  f : subfinite-enumeration X → subtype-enumeration X
  f (n , S , (m , m-emb) , (e , e-surj)) =
   n , (λ i → fiber m i , m-emb i) ,
   (e ∘ ⌜ φ ⌝ , ∘-is-surjection (equivs-are-surjections ⌜ φ ⌝-is-equiv) e-surj)
   where
    φ : (Σ i ꞉ Fin n , fiber m i) ≃ S
    φ = total-fiber-is-domain m

  g : subtype-enumeration X → subfinite-enumeration X
  g (n , A , e) = n , (Σ i ꞉ Fin n , A i holds) ,
                  (pr₁ , pr₁-is-embedding (λ i → holds-is-prop (A i))) , e

\end{code}

1a. A type that embeds into some Fin n is properly finite.

\begin{code}

is-subfinite : 𝓤 ̇ → 𝓤 ̇
is-subfinite X = ∃ n ꞉ ℕ , X ↪ Fin n

subfinite-types-are-properly-finite : {X : 𝓤 ̇ }
                                    → is-subfinite X
                                    → is-properly-finite X
subfinite-types-are-properly-finite {𝓤} {X} s = d , ∥∥-functor γ s
 where
  d : is-discrete X
  d = ∥∥-rec (being-discrete-is-prop (λ 𝓤 𝓥 → fe))
       (λ (n , m , m-emb) →
         embeddings-reflect-discreteness m m-emb Fin-is-discrete)
       s

  γ : (Σ n ꞉ ℕ , X ↪ Fin n) → subfinite-enumeration X
  γ (n , 𝕞) = n , X , 𝕞 , (id , id-is-surjection)

\end{code}

1b. Subtypes of properly finite types are properly finite. The new
subtype of Fin n is the preimage of the given one.

\begin{code}

properly-finite-subtypes : {X : 𝓤 ̇ } (A : X → 𝓥 ̇ )
                         → ((x : X) → is-prop (A x))
                         → is-properly-finite X
                         → is-properly-finite (Σ A)
properly-finite-subtypes {𝓤} {𝓥} {X} A A-is-prop-valued (d , s) =
 subtype-is-discrete A-is-prop-valued d , ∥∥-functor γ s
 where
  γ : subfinite-enumeration X → subfinite-enumeration (Σ A)
  γ (n , S , (m , m-emb) , (e , e-surj)) =
   n , (Σ s ꞉ S , A (e s)) ,
   (m ∘ pr₁ ,
    ∘-is-embedding (pr₁-is-embedding (λ s → A-is-prop-valued (e s))) m-emb) ,
   (pair-fun e (λ s a → a) ,
    pair-fun-surjection.pair-fun-is-surjection e (λ s a → a) pt
     e-surj (λ s → id-is-surjection))

\end{code}

1c. Binary products of properly finite types are properly finite,
because Fin m × Fin n is equivalent to some Fin k.

\begin{code}

properly-finite-products : {X : 𝓤 ̇ } {Y : 𝓥 ̇ }
                         → is-properly-finite X
                         → is-properly-finite Y
                         → is-properly-finite (X × Y)
properly-finite-products {𝓤} {𝓥} {X} {Y} (d , s) (d' , s') =
 ×-is-discrete d d' , ∥∥-functor₂ γ s s'
 where
  γ : subfinite-enumeration X
    → subfinite-enumeration Y
    → subfinite-enumeration (X × Y)
  γ (m , S , (μ , μ-emb) , (e , e-surj)) (n , T , (ν , ν-emb) , (e' , e'-surj))
   =
   pr₁ (×construction m n) , (S × T) ,
   (⌜ φ ⌝⁻¹ ∘ (λ (s , t) → μ s , ν t) ,
    ∘-is-embedding
     (×-is-embedding μ ν μ-emb ν-emb)
     (equivs-are-embeddings ⌜ φ ⌝⁻¹ (⌜⌝⁻¹-is-equiv φ))) ,
   (pair-fun e (λ _ → e') ,
    pair-fun-surjection.pair-fun-is-surjection e (λ _ → e') pt
     e-surj (λ _ → e'-surj))
   where
    φ : Fin (pr₁ (×construction m n)) ≃ Fin m × Fin n
    φ = pr₂ (×construction m n)

\end{code}

Closure under equivalence, within a universe and into a larger one,
and the two forms in which the next gate uses 1b and 1c.

\begin{code}

properly-finite-types-are-closed-under-equivalence
 : {X Y : 𝓤 ̇ }
 → X ≃ Y
 → is-properly-finite X
 → is-properly-finite Y
properly-finite-types-are-closed-under-equivalence {𝓤} {X} {Y} φ (d , s) =
 equiv-to-discrete φ d , ∥∥-functor γ s
 where
  γ : subfinite-enumeration X → subfinite-enumeration Y
  γ (n , S , 𝕞 , (e , e-surj)) =
   n , S , 𝕞 ,
   (⌜ φ ⌝ ∘ e , ∘-is-surjection e-surj (equivs-are-surjections ⌜ φ ⌝-is-equiv))

properly-finite-types-are-closed-under-equivalence'
 : {X : 𝓤 ̇ } {Y : 𝓤 ⊔ 𝓥 ̇ }
 → X ≃ Y
 → is-properly-finite X
 → is-properly-finite Y
properly-finite-types-are-closed-under-equivalence' {𝓤} {𝓥} {X} {Y} φ (d , s) =
 equiv-to-discrete φ d , ∥∥-functor γ s
 where
  γ : subfinite-enumeration X → subfinite-enumeration Y
  γ (n , S , (m , m-emb) , (e , e-surj)) =
   n , Lift 𝓥 S ,
   (m ∘ ⌜ ψ ⌝ ,
     ∘-is-embedding (equivs-are-embeddings ⌜ ψ ⌝ ⌜ ψ ⌝-is-equiv) m-emb) ,
   (⌜ φ ⌝ ∘ e ∘ ⌜ ψ ⌝ ,
    ∘-is-surjection
     (∘-is-surjection (equivs-are-surjections ⌜ ψ ⌝-is-equiv) e-surj)
     (equivs-are-surjections ⌜ φ ⌝-is-equiv))
   where
    ψ : Lift 𝓥 S ≃ S
    ψ = Lift-≃ 𝓥 S

properly-finite-subtypes-of-products
 : {X : 𝓤 ̇ } {Y : 𝓥 ̇ } (R : X → Y → 𝓦 ̇ )
 → ((x : X) (y : Y) → is-prop (R x y))
 → is-properly-finite X
 → is-properly-finite Y
 → is-properly-finite (Σ x ꞉ X , Σ y ꞉ Y , R x y)
properly-finite-subtypes-of-products R R-is-prop-valued i j =
 properly-finite-types-are-closed-under-equivalence Σ-assoc
  (properly-finite-subtypes (λ (x , y) → R x y)
    (λ (x , y) → R-is-prop-valued x y)
    (properly-finite-products i j))

properly-finite-sums-of-props
 : {X : 𝓤 ̇ } {Y : 𝓤 ⊔ 𝓥 ̇ } (R : X → 𝓥 ̇ )
 → ((x : X) → is-prop (R x))
 → Y ≃ Σ R
 → is-properly-finite X
 → is-properly-finite Y
properly-finite-sums-of-props R R-is-prop-valued φ i =
 properly-finite-types-are-closed-under-equivalence (≃-sym φ)
  (properly-finite-subtypes R R-is-prop-valued i)

\end{code}

Two small examples: Fin n and propositions are properly finite.

\begin{code}

Fin-is-properly-finite : (n : ℕ) → is-properly-finite (Fin n)
Fin-is-properly-finite n =
 subfinite-types-are-properly-finite ∣ n , id , id-is-embedding ∣

props-are-properly-finite : {P : 𝓤 ̇ } → is-prop P → is-properly-finite P
props-are-properly-finite i =
 subfinite-types-are-properly-finite
  ∣ 1 , (λ _ → 𝟎) ,
        maps-of-props-into-sets-are-embeddings (λ _ → 𝟎) i
         (discrete-types-are-sets Fin-is-discrete) ∣

\end{code}

Finite types, merely equivalent to some Fin n, are properly finite
(added at orbifold gate H8).

\begin{code}

is-finite : 𝓤 ̇ → 𝓤 ̇
is-finite X = ∥ finite-linear-order X ∥

finite-types-are-properly-finite : {X : 𝓤 ̇ } → is-finite X
                                 → is-properly-finite X
finite-types-are-properly-finite =
 ∥∥-rec being-properly-finite-is-prop
  (λ (n , φ) → properly-finite-types-are-closed-under-equivalence' (≃-sym φ)
                (Fin-is-properly-finite n))

\end{code}
