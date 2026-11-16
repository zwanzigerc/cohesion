Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 13 November 2026 (local time), for gate WG3 of Claude Fable
5.2's plan for the comparison of Weil algebras with presentations [1],
as reviewed by GPT-6 Astra [2], amended by Fable's addendum 01 [3] and
released by Astra [4]. The exported names, and the universes and
hypotheses of their statements, are those of the plan's statement
companion, with the explicit algebras of two compositions that Fable's
audit of WG1 calls for [5]; the proofs are Claude Opus 5.5's. See the
AI disclosure in gist.RealCohesion.index.

Consequences of the interface of presented algebras
---------------------------------------------------

The module is parametrized by an arbitrary instance pa of the interface
Presented-Algebras 𝓠 of gist.Orbifolds.PresentedAlgebras, with carriers
in any universe 𝓠. Every proof uses only the fields of pa: the relations
(P1), the universal property (P2) through hom-from-presented and the
uniqueness of homomorphisms on generators, and nothing about how an
instance is built. In particular no effectivity of a quotient is used,
and no instance is assumed to be a given algebra.

Homomorphisms to R and solutions (Myers's Remark 4.1.6 [6]).

  Sol g : the solutions in R of the equations g j = 0, a type in 𝓤₀.

  spectrum-of-presented-algebra : the spectrum of R⟨ g ⟩ is equivalent
  to Sol g. A homomorphism h goes to its values at the generators, which
  solve the equations by (P1), values-under-homs and values-in-R
  (points-of-the-spectrum-solve); a solution goes to the homomorphism of
  (P2) into R that takes the generators to it (point-of-solution). The
  two composites are identities by the uniqueness of homomorphisms on
  generators and by the values of (P2) at the generators.

  spectrum-of-presented-algebra-is-over-Rⁿ : the forward map is the
  restriction to the generators, by refl.

  ev₀, ev₀-on-generators, spectrum-of-presented-algebra-is-pointed : when
  the equations vanish at the origin, the point of the spectrum that
  sends every generator to 0, and the equivalence takes it to the origin.

  spectra-of-presented-algebras-are-small : so the spectrum, a type in 𝓠,
  is 𝓤₀-small in the sense of UF.Size, by the solution set itself. No
  resizing is used.

Translation. translate c g substitutes var i ⊕ con (c i) for the i-th
variable of every relation. translation-isomorphism : R⟨ translate c g ⟩
and R⟨ g ⟩ are isomorphic, for every vector c: the forward homomorphism
takes the i-th generator to the i-th generator minus c i, the backward one
the i-th generator to the i-th generator plus c i, both by (P2), and the
two composites are identities on the generators, hence everywhere. The
forward formula is translation-isomorphism-on-generators.

Centering (Myers's Lemma 4.1.3 [6]), for an algebra 𝓐 with a point π of
its spectrum and an isomorphism φ from R⟨ g ⟩: the augmentation values
c i are the values of π at the images of the generators, and the
centered relations are the translates of g by c. They vanish at the
origin, because c is the image of a point of the spectrum of R⟨ g ⟩, so
a solution (centered-relations-vanish-at-zero). The composite of the
translation isomorphism and φ is centering-isomorphism, and π composed
with it is the point ev₀ of the centered presentation
(centering-commutes-with-augmentations): on the i-th generator both give
c i - c i, that is, 0.

Adjoining powers. adjoin-powers f k adds to the relations f the powers
xᵢ ^ (k + 1) of the variables, after them, as SmoothLine's normalize
does. If these powers vanish already in R⟨ f ⟩, adjoining them changes
nothing: adjoining-vanishing-powers, an isomorphism that takes generators
to generators (adjoining-vanishing-powers-on-generators) and commutes
with the points ev₀ (adjoining-vanishing-powers-commutes-with-ev₀). Both
homomorphisms come from (P2): the forward one because the generators of
R⟨ f ⟩ satisfy f and the powers, the backward one because the generators
of R⟨ adjoin-powers f k ⟩ satisfy f, by join-left.

Notation. In centering-commutes-with-augmentations and
adjoining-vanishing-powers-commutes-with-ev₀ the composition _∘ₕ_ is
written with its three algebras, source, middle and target, which Agda
cannot infer from the types of homomorphisms, and so is ≅ₐ-trans in
centering-isomorphism [5]. The statements are the companion's.

Assumptions: function extensionality and propositional truncations, as
in SmoothLine, and the instance pa, which is an ordinary parameter. No
propositional extensionality, quotient, choice, univalence, resizing or
crisp datum is assumed, and the module adds no option and no postulate.

[1] Claude Fable 5.2. Plan: formalizing the comparison of Weil algebras
    with presentations, 13 November 2026, Section 4.3, with its
    statement companion, Section WG3 (plan SHA-256 b1662ecc…; companion
    SHA-256 47974af8…).
[2] GPT-6 Astra. Review of Fable's Weil plan, 13 November 2026
    (FABLE-WEIL-PLAN-REVIEW-01).
[3] Claude Fable 5.2. Addendum 01 to the plan, 13 November 2026
    (SHA-256 abf31923…).
[4] GPT-6 Astra. Release of gate WG3, 13 November 2026
    (SHA-256 628796c7…).
[5] Claude Fable 5.2. WG1 implementation audit, 13 November 2026,
    Section 3 (SHA-256 e87e594a…).
[6] David Jaz Myers. Orbifolds as microlinear types in synthetic
    differential cohesive homotopy type theory. arXiv:2205.15887v1.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import gist.Orbifolds.SmoothLine
 using (Commutative-Ring ; module smooth-line)
import gist.Orbifolds.PresentedAlgebras

module gist.Orbifolds.PresentedAlgebrasProperties
        (fe : Fun-Ext)
        (pt : propositional-truncations-exist)
        (𝓡 : Commutative-Ring)
        {𝓠 : Universe}
        (pa : gist.Orbifolds.PresentedAlgebras.Presented-Algebras fe pt 𝓡 𝓠)
       where

open import Fin.Type
open import Naturals.Addition using () renaming (_+_ to _+ᴺ_)
open import UF.Base
open import UF.Equiv
open import UF.Size using (_is_small)
open import UF.Subsingletons
open import UF.Subsingletons-FunExt

open PropositionalTruncation pt
open smooth-line fe pt 𝓡
open import gist.Orbifolds.Algebras fe pt 𝓡
open gist.Orbifolds.PresentedAlgebras fe pt 𝓡
open Presented-Algebras pa

\end{code}

Homomorphisms to R and solutions.

\begin{code}

Sol : {n m : ℕ} → (Fin m → Poly n) → 𝓤₀ ̇
Sol {n} {m} g = Σ a ꞉ (Fin n → R) , ((j : Fin m) → ⟦ g j ⟧ a ＝ 0ᴿ)

solutions-are-determined-by-their-points
 : {n m : ℕ} (g : Fin m → Poly n) (σ τ : Sol g) → pr₁ σ ＝ pr₁ τ → σ ＝ τ
solutions-are-determined-by-their-points g σ τ =
 to-subtype-＝ (λ a → Π-is-prop fe (λ j → R-is-set))

points-of-the-spectrum-solve
 : {n m : ℕ} (g : Fin m → Poly n) (h : Specᴿ R⟨ g ⟩) (j : Fin m)
 → ⟦ g j ⟧ (pr₁ h ∘ gen g) ＝ 0ᴿ
points-of-the-spectrum-solve g h j =
 (values-in-R (g j) (pr₁ h ∘ gen g))⁻¹
 ∙ (values-under-homs R⟨ g ⟩ R-as-algebra h (g j) (gen g))⁻¹
 ∙ ap (pr₁ h) (relations-hold g j)
 ∙ homs-preserve-0 R⟨ g ⟩ R-as-algebra h

solutions-solve-in-R
 : {n m : ℕ} (g : Fin m → Poly n) (σ : Sol g) (j : Fin m)
 → ⟦ g j ⟧[ R-as-algebra ] (pr₁ σ) ＝ Algebra.0ᴬ R-as-algebra
solutions-solve-in-R g σ j = values-in-R (g j) (pr₁ σ) ∙ pr₂ σ j

point-of-solution : {n m : ℕ} (g : Fin m → Poly n) → Sol g → Specᴿ R⟨ g ⟩
point-of-solution g σ =
 hom-from-presented pa g R-as-algebra (pr₁ σ) (solutions-solve-in-R g σ)

point-of-solution-on-generators
 : {n m : ℕ} (g : Fin m → Poly n) (σ : Sol g)
 → pr₁ (point-of-solution g σ) ∘ gen g ∼ pr₁ σ
point-of-solution-on-generators g σ =
 hom-from-presented-on-generators pa g R-as-algebra (pr₁ σ)
  (solutions-solve-in-R g σ)

spectrum-of-presented-algebra
 : {n m : ℕ} (g : Fin m → Poly n) → Specᴿ R⟨ g ⟩ ≃ Sol g
spectrum-of-presented-algebra g = qinveq to-Sol (point-of-solution g , η , ε)
 where
  to-Sol : Specᴿ R⟨ g ⟩ → Sol g
  to-Sol h = (pr₁ h ∘ gen g) , points-of-the-spectrum-solve g h

  η : point-of-solution g ∘ to-Sol ∼ id
  η h = homs-from-presented-are-determined-by-generators pa g R-as-algebra
         (point-of-solution g (to-Sol h)) h
         (point-of-solution-on-generators g (to-Sol h))

  ε : to-Sol ∘ point-of-solution g ∼ id
  ε σ = solutions-are-determined-by-their-points g
         (to-Sol (point-of-solution g σ)) σ
         (dfunext fe (point-of-solution-on-generators g σ))

spectrum-of-presented-algebra-is-over-Rⁿ
 : {n m : ℕ} (g : Fin m → Poly n) (h : Specᴿ R⟨ g ⟩)
 → pr₁ (⌜ spectrum-of-presented-algebra g ⌝ h) ＝ pr₁ h ∘ gen g
spectrum-of-presented-algebra-is-over-Rⁿ g h = refl

ev₀ : {n m : ℕ} (g : Fin m → Poly n)
    → ((j : Fin m) → ⟦ g j ⟧ (λ _ → 0ᴿ) ＝ 0ᴿ)
    → Specᴿ R⟨ g ⟩
ev₀ g z = point-of-solution g ((λ _ → 0ᴿ) , z)

ev₀-on-generators
 : {n m : ℕ} (g : Fin m → Poly n) (z : (j : Fin m) → ⟦ g j ⟧ (λ _ → 0ᴿ) ＝ 0ᴿ)
   (i : Fin n)
 → pr₁ (ev₀ g z) (gen g i) ＝ 0ᴿ
ev₀-on-generators g z = point-of-solution-on-generators g ((λ _ → 0ᴿ) , z)

spectrum-of-presented-algebra-is-pointed
 : {n m : ℕ} (g : Fin m → Poly n) (z : (j : Fin m) → ⟦ g j ⟧ (λ _ → 0ᴿ) ＝ 0ᴿ)
 → ⌜ spectrum-of-presented-algebra g ⌝ (ev₀ g z) ＝ ((λ _ → 0ᴿ) , z)
spectrum-of-presented-algebra-is-pointed g z =
 solutions-are-determined-by-their-points g
  (⌜ spectrum-of-presented-algebra g ⌝ (ev₀ g z)) ((λ _ → 0ᴿ) , z)
  (dfunext fe (ev₀-on-generators g z))

spectra-of-presented-algebras-are-small
 : {n m : ℕ} (g : Fin m → Poly n) → (Specᴿ R⟨ g ⟩) is 𝓤₀ small
spectra-of-presented-algebras-are-small g =
 Sol g , ≃-sym (spectrum-of-presented-algebra g)

\end{code}

Translation.

\begin{code}

translate : {n m : ℕ} → (Fin n → R) → (Fin m → Poly n) → (Fin m → Poly n)
translate c g j = substitute (λ i → var i ⊕ con (c i)) (g j)

values-of-translates
 : {n m : ℕ} (c : Fin n → R) (g : Fin m → Poly n) (j : Fin m) (a : Fin n → R)
 → ⟦ translate c g j ⟧ a ＝ ⟦ g j ⟧ (λ i → a i +ᴿ c i)
values-of-translates c g j a =
 (values-in-R (translate c g j) a)⁻¹
 ∙ values-of-substitutions R-as-algebra (λ i → var i ⊕ con (c i)) (g j) a
 ∙ values-in-R (g j) (λ i → a i +ᴿ c i)

module _ {𝓦 : Universe} (𝓐 : Algebra 𝓦) where

 open Algebra 𝓐

 adding-and-removing-a-constant
  : (x : A) (r : R) → (x +ᴬ ι r) +ᴬ ι (-ᴿ r) ＝ x
 adding-and-removing-a-constant x r =
  +ᴬ-assoc x (ι r) (ι (-ᴿ r))
  ∙ ap (x +ᴬ_) ((ι-preserves-+ r (-ᴿ r))⁻¹
                ∙ ap ι (+-inverse r)
                ∙ ι-preserves-0 𝓐)
  ∙ +ᴬ-unit x

 removing-and-adding-a-constant
  : (x : A) (r : R) → (x +ᴬ ι (-ᴿ r)) +ᴬ ι r ＝ x
 removing-and-adding-a-constant x r =
  +ᴬ-assoc x (ι (-ᴿ r)) (ι r)
  ∙ ap (x +ᴬ_) ((ι-preserves-+ (-ᴿ r) r)⁻¹
                ∙ ap ι (+-comm (-ᴿ r) r ∙ +-inverse r)
                ∙ ι-preserves-0 𝓐)
  ∙ +ᴬ-unit x

module _ {n m : ℕ} (c : Fin n → R) (g : Fin m → Poly n) where

 private
  𝓢 𝓖 : Algebra 𝓠
  𝓢 = R⟨ translate c g ⟩
  𝓖 = R⟨ g ⟩

  module T = Algebra 𝓢
  module G = Algebra 𝓖

  shift : Fin n → Poly n
  shift i = var i ⊕ con (c i)

 translated-generators : Fin n → ⟨ R⟨ g ⟩ ⟩
 translated-generators i = gen g i G.+ᴬ G.ι (-ᴿ c i)

 untranslated-generators : Fin n → ⟨ R⟨ translate c g ⟩ ⟩
 untranslated-generators i = gen (translate c g) i T.+ᴬ T.ι (c i)

 translated-generators-satisfy-the-translates
  : (j : Fin m)
  → ⟦ translate c g j ⟧[ R⟨ g ⟩ ] translated-generators ＝ Algebra.0ᴬ R⟨ g ⟩
 translated-generators-satisfy-the-translates j =
  values-of-substitutions 𝓖 shift (g j) translated-generators
  ∙ values-at-equal-points 𝓖 (g j)
     (λ i → ⟦ shift i ⟧[ 𝓖 ] translated-generators) (gen g)
     (λ i → removing-and-adding-a-constant 𝓖 (gen g i) (c i))
  ∙ relations-hold g j

 untranslated-generators-satisfy-the-relations
  : (j : Fin m)
  → ⟦ g j ⟧[ R⟨ translate c g ⟩ ] untranslated-generators
  ＝ Algebra.0ᴬ R⟨ translate c g ⟩
 untranslated-generators-satisfy-the-relations j =
  (values-of-substitutions 𝓢 shift (g j) (gen (translate c g)))⁻¹
  ∙ relations-hold (translate c g) j

 translation-forward : Hom R⟨ translate c g ⟩ R⟨ g ⟩
 translation-forward =
  hom-from-presented pa (translate c g) 𝓖 translated-generators
   translated-generators-satisfy-the-translates

 translation-backward : Hom R⟨ g ⟩ R⟨ translate c g ⟩
 translation-backward =
  hom-from-presented pa g 𝓢 untranslated-generators
   untranslated-generators-satisfy-the-relations

 translation-forward-on-generators
  : pr₁ translation-forward ∘ gen (translate c g) ∼ translated-generators
 translation-forward-on-generators =
  hom-from-presented-on-generators pa (translate c g) 𝓖 translated-generators
   translated-generators-satisfy-the-translates

 translation-backward-on-generators
  : pr₁ translation-backward ∘ gen g ∼ untranslated-generators
 translation-backward-on-generators =
  hom-from-presented-on-generators pa g 𝓢 untranslated-generators
   untranslated-generators-satisfy-the-relations

 translation-isomorphism : R⟨ translate c g ⟩ ≅ₐ R⟨ g ⟩
 translation-isomorphism =
  translation-forward ,
  translation-backward ,
  backward-after-forward ,
  forward-after-backward
  where
   fw : Hom 𝓢 𝓖
   fw = translation-forward

   bw : Hom 𝓖 𝓢
   bw = translation-backward

   backward-after-forward : pr₁ bw ∘ pr₁ fw ∼ id
   backward-after-forward =
    happly (ap pr₁ (homs-from-presented-are-determined-by-generators
                     pa (translate c g) 𝓢
                     (_∘ₕ_ {𝓐 = 𝓢} {𝓑 = 𝓖} {𝓒 = 𝓢} bw fw) (id-hom 𝓢)
                     γ))
    where
     γ : (i : Fin n) → pr₁ bw (pr₁ fw (gen (translate c g) i))
                     ＝ gen (translate c g) i
     γ i = ap (pr₁ bw) (translation-forward-on-generators i)
         ∙ homs-preserve-+ 𝓖 𝓢 bw (gen g i) (G.ι (-ᴿ c i))
         ∙ ap₂ T._+ᴬ_ (translation-backward-on-generators i)
                      (homs-preserve-ι 𝓖 𝓢 bw (-ᴿ c i))
         ∙ adding-and-removing-a-constant 𝓢 (gen (translate c g) i) (c i)

   forward-after-backward : pr₁ fw ∘ pr₁ bw ∼ id
   forward-after-backward =
    happly (ap pr₁ (homs-from-presented-are-determined-by-generators
                     pa g 𝓖
                     (_∘ₕ_ {𝓐 = 𝓖} {𝓑 = 𝓢} {𝓒 = 𝓖} fw bw) (id-hom 𝓖)
                     γ))
    where
     γ : (i : Fin n) → pr₁ fw (pr₁ bw (gen g i)) ＝ gen g i
     γ i = ap (pr₁ fw) (translation-backward-on-generators i)
         ∙ homs-preserve-+ 𝓢 𝓖 fw (gen (translate c g) i) (T.ι (c i))
         ∙ ap₂ G._+ᴬ_ (translation-forward-on-generators i)
                      (homs-preserve-ι 𝓢 𝓖 fw (c i))
         ∙ removing-and-adding-a-constant 𝓖 (gen g i) (c i)

translation-isomorphism-on-generators
 : {n m : ℕ} (c : Fin n → R) (g : Fin m → Poly n) (i : Fin n)
 → pr₁ (pr₁ (translation-isomorphism c g)) (gen (translate c g) i)
 ＝ Algebra._+ᴬ_ R⟨ g ⟩ (gen g i) (Algebra.ι R⟨ g ⟩ (-ᴿ c i))
translation-isomorphism-on-generators c g =
 translation-forward-on-generators c g

\end{code}

Centering, for a given presentation.

\begin{code}

module _ {𝓦 : Universe} (𝓐 : Algebra 𝓦) (π : Specᴿ 𝓐)
         {n m : ℕ} (g : Fin m → Poly n) (φ : R⟨ g ⟩ ≅ₐ 𝓐)
       where

 private
  χ : Specᴿ R⟨ g ⟩
  χ = _∘ₕ_ {𝓐 = R⟨ g ⟩} {𝓑 = 𝓐} {𝓒 = R-as-algebra} π (pr₁ φ)

 augmentation-values : Fin n → R
 augmentation-values i = pr₁ π (pr₁ (pr₁ φ) (gen g i))

 centered-relations : Fin m → Poly n
 centered-relations = translate augmentation-values g

 centered-relations-vanish-at-zero
  : (j : Fin m) → ⟦ centered-relations j ⟧ (λ _ → 0ᴿ) ＝ 0ᴿ
 centered-relations-vanish-at-zero j =
  values-of-translates augmentation-values g j (λ _ → 0ᴿ)
  ∙ ap ⟦ g j ⟧ (dfunext fe (λ i → +-unit-left (augmentation-values i)))
  ∙ points-of-the-spectrum-solve g χ j

 centering-isomorphism : R⟨ centered-relations ⟩ ≅ₐ 𝓐
 centering-isomorphism =
  ≅ₐ-trans {𝓐 = R⟨ centered-relations ⟩} {𝓑 = R⟨ g ⟩} {𝓒 = 𝓐}
   (translation-isomorphism augmentation-values g) φ

 centering-commutes-with-augmentations
  : _∘ₕ_ {𝓐 = R⟨ centered-relations ⟩} {𝓑 = 𝓐} {𝓒 = R-as-algebra}
     π (pr₁ centering-isomorphism)
  ＝ ev₀ centered-relations centered-relations-vanish-at-zero
 centering-commutes-with-augmentations =
  homs-from-presented-are-determined-by-generators pa centered-relations
   R-as-algebra _ _ γ
  where
   c : Fin n → R
   c = augmentation-values

   φ₁ : ⟨ R⟨ g ⟩ ⟩ → ⟨ 𝓐 ⟩
   φ₁ = pr₁ (pr₁ φ)

   ι-g : R → ⟨ R⟨ g ⟩ ⟩
   ι-g = Algebra.ι R⟨ g ⟩

   γ : (i : Fin n)
     → pr₁ π (φ₁ (pr₁ (translation-forward c g) (gen centered-relations i)))
     ＝ pr₁ (ev₀ centered-relations centered-relations-vanish-at-zero)
            (gen centered-relations i)
   γ i = ap (pr₁ π ∘ φ₁) (translation-forward-on-generators c g i)
       ∙ ap (pr₁ π) (homs-preserve-+ R⟨ g ⟩ 𝓐 (pr₁ φ) (gen g i) (ι-g (-ᴿ c i)))
       ∙ homs-preserve-+ 𝓐 R-as-algebra π (φ₁ (gen g i)) (φ₁ (ι-g (-ᴿ c i)))
       ∙ ap (c i +ᴿ_) (ap (pr₁ π) (homs-preserve-ι R⟨ g ⟩ 𝓐 (pr₁ φ) (-ᴿ c i))
                       ∙ homs-preserve-ι 𝓐 R-as-algebra π (-ᴿ c i))
       ∙ +-inverse (c i)
       ∙ (ev₀-on-generators centered-relations
           centered-relations-vanish-at-zero i)⁻¹

\end{code}

Adjoining powers.

\begin{code}

adjoin-powers : {n m : ℕ} → (Fin m → Poly n) → ℕ → (Fin (m +ᴺ n) → Poly n)
adjoin-powers f k = join f (λ i → power (var i) (succ k))

module _ {n m : ℕ} (f : Fin m → Poly n) (k : ℕ) where

 private
  𝓕 𝓟 : Algebra 𝓠
  𝓕 = R⟨ f ⟩
  𝓟 = R⟨ adjoin-powers f k ⟩

  powers : Fin n → Poly n
  powers i = power (var i) (succ k)

 relations-hold-after-adjoining
  : (j : Fin m)
  → ⟦ f j ⟧[ R⟨ adjoin-powers f k ⟩ ] (gen (adjoin-powers f k))
  ＝ Algebra.0ᴬ R⟨ adjoin-powers f k ⟩
 relations-hold-after-adjoining j =
  transport (λ p → ⟦ p ⟧[ 𝓟 ] (gen (adjoin-powers f k)) ＝ Algebra.0ᴬ 𝓟)
   (join-left f powers j)
   (relations-hold (adjoin-powers f k) (left-index j))

 adjoining-backward : Hom R⟨ f ⟩ R⟨ adjoin-powers f k ⟩
 adjoining-backward =
  hom-from-presented pa f 𝓟 (gen (adjoin-powers f k))
   relations-hold-after-adjoining

 adjoining-backward-on-generators
  : pr₁ adjoining-backward ∘ gen f ∼ gen (adjoin-powers f k)
 adjoining-backward-on-generators =
  hom-from-presented-on-generators pa f 𝓟 (gen (adjoin-powers f k))
   relations-hold-after-adjoining

 module _ (ν : (i : Fin n) → _^ᴬ_ R⟨ f ⟩ (gen f i) (succ k) ＝ Algebra.0ᴬ R⟨ f ⟩)
        where

  powers-vanish-at-the-generators
   : (j : Fin (m +ᴺ n))
   → ⟦ adjoin-powers f k j ⟧[ R⟨ f ⟩ ] (gen f) ＝ Algebra.0ᴬ R⟨ f ⟩
  powers-vanish-at-the-generators =
   join-induction (λ p → ⟦ p ⟧[ 𝓕 ] (gen f) ＝ Algebra.0ᴬ 𝓕) f powers
    (relations-hold f)
    (λ i → value-of-power-in-algebras 𝓕 (var i) (succ k) (gen f) ∙ ν i)

  adjoining-forward : Hom R⟨ adjoin-powers f k ⟩ R⟨ f ⟩
  adjoining-forward =
   hom-from-presented pa (adjoin-powers f k) 𝓕 (gen f)
    powers-vanish-at-the-generators

  adjoining-forward-on-generators
   : pr₁ adjoining-forward ∘ gen (adjoin-powers f k) ∼ gen f
  adjoining-forward-on-generators =
   hom-from-presented-on-generators pa (adjoin-powers f k) 𝓕 (gen f)
    powers-vanish-at-the-generators

  adjoining-vanishing-powers : R⟨ adjoin-powers f k ⟩ ≅ₐ R⟨ f ⟩
  adjoining-vanishing-powers =
   adjoining-forward ,
   adjoining-backward ,
   backward-after-forward ,
   forward-after-backward
   where
    fw : Hom 𝓟 𝓕
    fw = adjoining-forward

    bw : Hom 𝓕 𝓟
    bw = adjoining-backward

    backward-after-forward : pr₁ bw ∘ pr₁ fw ∼ id
    backward-after-forward =
     happly (ap pr₁ (homs-from-presented-are-determined-by-generators
                      pa (adjoin-powers f k) 𝓟
                      (_∘ₕ_ {𝓐 = 𝓟} {𝓑 = 𝓕} {𝓒 = 𝓟} bw fw) (id-hom 𝓟)
                      (λ i → ap (pr₁ bw) (adjoining-forward-on-generators i)
                           ∙ adjoining-backward-on-generators i)))

    forward-after-backward : pr₁ fw ∘ pr₁ bw ∼ id
    forward-after-backward =
     happly (ap pr₁ (homs-from-presented-are-determined-by-generators
                      pa f 𝓕
                      (_∘ₕ_ {𝓐 = 𝓕} {𝓑 = 𝓟} {𝓒 = 𝓕} fw bw) (id-hom 𝓕)
                      (λ i → ap (pr₁ fw) (adjoining-backward-on-generators i)
                           ∙ adjoining-forward-on-generators i)))

  adjoining-vanishing-powers-on-generators
   : (i : Fin n)
   → pr₁ (pr₁ adjoining-vanishing-powers) (gen (adjoin-powers f k) i)
   ＝ gen f i
  adjoining-vanishing-powers-on-generators = adjoining-forward-on-generators

  adjoining-vanishing-powers-commutes-with-ev₀
   : (z : (j : Fin m) → ⟦ f j ⟧ (λ _ → 0ᴿ) ＝ 0ᴿ)
     (z' : (j : Fin (m +ᴺ n)) → ⟦ adjoin-powers f k j ⟧ (λ _ → 0ᴿ) ＝ 0ᴿ)
   → _∘ₕ_ {𝓐 = R⟨ adjoin-powers f k ⟩} {𝓑 = R⟨ f ⟩} {𝓒 = R-as-algebra}
      (ev₀ f z) (pr₁ adjoining-vanishing-powers)
   ＝ ev₀ (adjoin-powers f k) z'
  adjoining-vanishing-powers-commutes-with-ev₀ z z' =
   homs-from-presented-are-determined-by-generators pa (adjoin-powers f k)
    R-as-algebra _ _
    (λ i → ap (pr₁ (ev₀ f z)) (adjoining-forward-on-generators i)
         ∙ ev₀-on-generators f z i
         ∙ (ev₀-on-generators (adjoin-powers f k) z' i)⁻¹)

\end{code}
