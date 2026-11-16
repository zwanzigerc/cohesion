Claude Fable 5.2, an AI model made by Anthropic, prompted by Colin
Zwanziger, 11 November 2026 (gate G15 of Fable's blueprint addendum).
Added to the folder by Claude Opus 5.5 on 12 November 2026, at Colin
Zwanziger's decision, with the code unchanged and two sentences of the
prose changed: they pointed to a module DiscreteSetsFlatSplit, with
--flat-split, which is not part of the folder; its three results are
stated in gist.RealCohesion.Theorems in --safe mode. On 13 November
2026, in the consolidation after the final audits, Claude Opus 5.5
made the proof of discrete-types-are-ℝ-null an instance of
gist.RealCohesion.BooleanTests, and maps-from-ℝ-to-𝟚-are-constant one
of gist.RealCohesion.PunctualCohesion for the one generator ℝ; names
and types are unchanged. He also added the module under-C1, in which
maps from ℝ to 𝟚 are constant under Axiom C1 and a merely strictly
rising generator path, for parts (a) and (c) (W3 of Claude Fable 5.2's
consolidation plan, released by GPT-6 Astra). See the AI disclosure in
gist.RealCohesion.index.

Shulman's Lemma 8.15 [1], with its scope.

Lemma 8.15 is printed as: assuming crisp excluded middle and Axiom C1,
a set is discrete if and only if it has decidable equality. Here
"discrete" is meant for an arbitrary type, not necessarily crisp, in
the sense of [1, Definition 8.2]: null with respect to the generators,
which in real cohesion is ℝ-null. In TypeTopology "discrete" means
"has decidable equality", so we say "ℝ-null" for Shulman's notion.

The lemma has three parts, of which the third is a correction.

 (a) Decidable equality gives ℝ-nullity. This holds for every type,
     crisp or not. It is the second half of the printed proof and
     uses only that every map from ℝ to 𝟚 is constant. We prove it
     below (discrete-types-are-ℝ-null).

 (b) A ♭-discrete crisp set has decidable equality, under crisp
     excluded middle. This is the first half of the printed proof,
     whose step "given x, y : A we may assume they are crisp" needs
     the set A to be crisp. It is already formalized, as
     ♭-discrete-sets-are-discrete in gist.CohesiveApartness.Flat.

 (c) Without crispness the implication of (b) is refutable. For a
     real number x, the type (0 < x) → 𝟚 is an ℝ-null set, because
     ℝ-null types are closed under products, and its two constant
     functions are equal exactly if ¬ (0 < x). So if every ℝ-null set
     had decidable equality, we could define a map from ℝ to 𝟚 which
     takes the value ₀ at 0 and the value ₁ at 1. We prove this below
     (ℝ-null-sets-need-not-be-discrete). The observation that the
     printed proof needs a crisp set, and the example of the type
     P → 𝟚, are due to GPT-6 Astra.

Parts (a) and (c) are first proved from the hypothesis that every map
from ℝ to 𝟚 is constant. This holds under Axiom R♭, because 𝟚 is
♭-discrete, and the last part of the module restates all three parts
under Axiom R♭. It also holds under Axiom C1 for an ordinary family of
pointed generators with a strictly rising generator path in ℝ, merely,
by the transfer lemma for sets of gist.RealCohesion.Constancy (module
under-C1), which gives parts (a) and (c) there. The converse of part
(a) for crisp sets uses the converse half of Axiom R♭, that ℝ-null
crisp types are ♭-discrete, which Axiom C1 does not give.
gist.RealCohesion.Theorems discharges the hypothesis that 𝟚 is
♭-discrete, by the native ♯ of Agda 2.9.0
(gist.CohesiveApartness.CrispInduction).

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.DiscreteSets
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
       where

open import DedekindReals.Order fe pe pt
open import DedekindReals.Type fe pe pt
open import MLTT.Two-Properties
open import Notation.Order
open import UF.Base
open import UF.DiscreteAndSeparated
open import UF.Sets
open import UF.Sets-Properties
open import gist.CohesiveApartness.Flat
open import gist.RealCohesion.BooleanTests
 using (maps-into-types-with-decidable-equality-are-constant)
import gist.RealCohesion.PunctualCohesion fe as PC
open import gist.RealCohesion.Constancy fe pe pt
 using (Rising-Generator-Path ; module transfer)

open PropositionalTruncation pt

Maps-From-ℝ-To-𝟚-Are-Constant : 𝓤₁ ̇
Maps-From-ℝ-To-𝟚-Are-Constant = (g : ℝ → 𝟚) (x : ℝ) → g x ＝ g 0ℝ

\end{code}

The characteristic function of a decision.

\begin{code}

χ : {𝓤 : Universe} {P : 𝓤 ̇ } → is-decidable P → 𝟚
χ (inl _) = ₁
χ (inr _) = ₀

χ-is-₁-gives-holds
 : {𝓤 : Universe} {P : 𝓤 ̇ } (δ : is-decidable P) → χ δ ＝ ₁ → P
χ-is-₁-gives-holds (inl p) _ = p
χ-is-₁-gives-holds (inr _) e = 𝟘-elim (zero-is-not-one e)

holds-gives-χ-is-₁
 : {𝓤 : Universe} {P : 𝓤 ̇ } (δ : is-decidable P) → P → χ δ ＝ ₁
holds-gives-χ-is-₁ (inl _) _ = refl
holds-gives-χ-is-₁ (inr ν) p = 𝟘-elim (ν p)

fails-gives-χ-is-₀
 : {𝓤 : Universe} {P : 𝓤 ̇ } (δ : is-decidable P) → ¬ P → χ δ ＝ ₀
fails-gives-χ-is-₀ (inl p) ν = 𝟘-elim (ν p)
fails-gives-χ-is-₀ (inr _) _ = refl

\end{code}

Part (a), by the Boolean test of gist.RealCohesion.BooleanTests at the
generator ℝ pointed by 0.

\begin{code}

discrete-types-are-ℝ-null
 : {𝓤 : Universe}
 → Maps-From-ℝ-To-𝟚-Are-Constant
 → (A : 𝓤 ̇ ) → is-discrete A → is-null ℝ A
discrete-types-are-ℝ-null c A d =
 rl-implication (null-iff-maps-are-constant fe ℝ 0ℝ A)
  (maps-into-types-with-decidable-equality-are-constant ℝ 0ℝ c A d)

\end{code}

Part (c). The ℝ-null types are closed under exponentials, and the two
constant functions P → 𝟚 are equal exactly if P fails.

\begin{code}

exponentials-of-𝟚-are-ℝ-null
 : {𝓤 : Universe}
 → Maps-From-ℝ-To-𝟚-Are-Constant
 → (P : 𝓤 ̇ ) → is-null ℝ (P → 𝟚)
exponentials-of-𝟚-are-ℝ-null c P =
 rl-implication (null-iff-maps-are-constant fe ℝ 0ℝ (P → 𝟚))
  (λ f x → dfunext fe (λ p → c (λ r → f r p) x))

ℝ-null-sets-need-not-be-discrete
 : Maps-From-ℝ-To-𝟚-Are-Constant
 → ¬ ((A : 𝓤₀ ̇ ) → is-set A → is-null ℝ A → is-discrete A)
ℝ-null-sets-need-not-be-discrete c φ = zero-is-not-one III
 where
  A : ℝ → 𝓤₀ ̇
  A x = (0ℝ < x) → 𝟚

  δ : (x : ℝ) → is-decidable ((λ (_ : 0ℝ < x) → ₀) ＝ (λ _ → ₁))
  δ x = φ (A x) (Π-is-set fe (λ _ → 𝟚-is-set))
         (exponentials-of-𝟚-are-ℝ-null c (0ℝ < x))
         (λ _ → ₀) (λ _ → ₁)

  g : ℝ → 𝟚
  g x = χ (δ x)

  I : g 0ℝ ＝ ₁
  I = holds-gives-χ-is-₁ (δ 0ℝ)
       (dfunext fe (λ l → 𝟘-elim (<ℝ-irreflexive 0ℝ l)))

  II : g 1ℝ ＝ ₀
  II = fails-gives-χ-is-₀ (δ 1ℝ)
        (λ e → zero-is-not-one (happly e ℝ-zero-less-than-one))

  III : ₀ ＝ ₁
  III = ₀    ＝⟨ II ⁻¹ ⟩
        g 1ℝ ＝⟨ c g 1ℝ ⟩
        g 0ℝ ＝⟨ I ⟩
        ₁    ∎

\end{code}

Parts (a) and (c) under Axiom C1 for an ordinary family R of pointed
generators and the ♭-discreteness of 𝟚, with a strictly rising
generator path in ℝ, merely: maps from a generator to the ♭-discrete
set 𝟚 are constant (gist.RealCohesion.PunctualCohesion), so maps from
ℝ to 𝟚 are constant, by the transfer lemma for sets.

\begin{code}

module under-C1 {𝓥 𝓦 : Universe} {J : 𝓥 ̇ } (R : J → 𝓦 ̇ ) (c1 : Axiom-C1 R)
                (𝟚-is-♭-discrete : is-♭-discrete 𝟚)
                (nc : ∥ Rising-Generator-Path R ∥)
              where

 open Axiom-C1 c1

 maps-from-ℝ-to-𝟚-are-constant : Maps-From-ℝ-To-𝟚-Are-Constant
 maps-from-ℝ-to-𝟚-are-constant g x = ∥∥-rec 𝟚-is-set γ nc
  where
   γ : Rising-Generator-Path R → g x ＝ g 0ℝ
   γ (j , h , a , b , l) =
    transfer.constancy-transfers-along-a-strict-rise (base-point j) 𝟚-is-set
     (PC.generator-maps-are-constant R c1 𝟚 𝟚-is-♭-discrete j) h a b g l x 0ℝ

 discrete-types-are-ℝ-null-under-C1
  : {𝓤 : Universe} (A : 𝓤 ̇ ) → is-discrete A → is-null ℝ A
 discrete-types-are-ℝ-null-under-C1 =
  discrete-types-are-ℝ-null maps-from-ℝ-to-𝟚-are-constant

 ℝ-null-sets-need-not-be-discrete-under-C1
  : ¬ ((A : 𝓤₀ ̇ ) → is-set A → is-null ℝ A → is-discrete A)
 ℝ-null-sets-need-not-be-discrete-under-C1 =
  ℝ-null-sets-need-not-be-discrete maps-from-ℝ-to-𝟚-are-constant

\end{code}

The same three parts under Axiom R♭, in the form of singly generated
punctual cohesion with generator ℝ pointed by 0. That 𝟚 is ♭-discrete
is a hypothesis here, as elsewhere in this folder; it is
𝟚-is-♭-discrete of gist.CohesiveApartness.CrispInduction, which
gist.RealCohesion.Theorems uses.

\begin{code}

module _ (r♭ : Singly-Generated-Punctual-Cohesion ℝ 0ℝ)
         (𝟚-is-♭-discrete : is-♭-discrete 𝟚)
       where

 maps-from-ℝ-to-𝟚-are-constant : Maps-From-ℝ-To-𝟚-Are-Constant
 maps-from-ℝ-to-𝟚-are-constant =
  PC.generator-maps-are-constant (λ (_ : 𝟙 {𝓤₀}) → ℝ)
   (singly-generated-punctual-cohesion-gives-Axiom-C1 fe ℝ 0ℝ r♭)
   𝟚 𝟚-is-♭-discrete ⋆

 discrete-types-are-ℝ-null-under-R♭
  : {𝓤 : Universe} (A : 𝓤 ̇ ) → is-discrete A → is-null ℝ A
 discrete-types-are-ℝ-null-under-R♭ =
  discrete-types-are-ℝ-null maps-from-ℝ-to-𝟚-are-constant

 crisp-ℝ-null-sets-are-discrete
  : {@♭ 𝓤 : Universe}
  → Crisp-EM 𝓤
  → (@♭ A : 𝓤 ̇ ) → @♭ is-set A → is-null ℝ A → is-discrete A
 crisp-ℝ-null-sets-are-discrete cem A A-is-set n =
  ♭-discrete-sets-are-discrete cem A A-is-set
   (rl-implication (r♭ A)
     (lr-implication (null-iff-maps-are-constant fe ℝ 0ℝ A) n))

 ℝ-null-sets-need-not-be-discrete-under-R♭
  : ¬ ((A : 𝓤₀ ̇ ) → is-set A → is-null ℝ A → is-discrete A)
 ℝ-null-sets-need-not-be-discrete-under-R♭ =
  ℝ-null-sets-need-not-be-discrete maps-from-ℝ-to-𝟚-are-constant

\end{code}

So Lemma 8.15 holds for crisp sets, in both directions, and its
direction from ℝ-nullity to decidable equality fails for sets that
are not crisp. Nothing in this module uses crisp excluded middle
except crisp-ℝ-null-sets-are-discrete, and the refutation uses
neither excluded middle nor univalence.
