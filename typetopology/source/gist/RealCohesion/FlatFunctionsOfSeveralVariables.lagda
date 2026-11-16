Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. See the AI disclosure in
gist.RealCohesion.index.

The canonical map ♭ (ℝⁿ → ℝ) → (♭ ℝⁿ → ♭ ℝ) is injective, from Axiom R♭
alone, and every continuous map is one of its values, from crisp
excluded middle and Axiom R♭. These are the first part of Theorem 3.3
of the write-up [1] without crisp excluded middle, gate G20 of Claude
Fable 5.2's second addendum [2], and its third part, gate G21.

The exact statement. Theorem 3.3 of [1] says, under crisp excluded
middle and Axiom R♭, that for every crisp n the canonical map
♭ (ℝⁿ → ℝ) → (♭ ℝⁿ → ♭ ℝ) is injective, that its values are ε-δ
continuous, and that every ε-δ continuous map is a value (its image
consists of the ε-δ continuous maps). Remark 7.18 (iii) of [1] records
that the first two parts hold from Axiom R♭ alone. The formal
statements here are ♭-apply-is-injective', the first part from Axiom
R♭ alone, and continuous-maps-are-values', the third part, from crisp
excluded middle for 𝓤₀ and Axiom R♭, with continuity in the sense of
gist.RealCohesion.ShulmanWeakeningsStatements (the supremum norm,
rational ε and δ). gist.RealCohesion.Theorems states the first part
with the second (gate G24) as the target
Target-3-3-embedding-and-continuity-from-R♭-alone, and all three parts
as the target Target-3-3, of
gist.RealCohesion.ShulmanWeakeningsStatements.

The proof of the first part is the addendum's [2, §3, G20], for n
variables as gist.RealCohesion.FlatRealFunctions does it for one. Crisp
functions F and G that agree at crisp points agree at rational points,
which are crisp up to equality (gist.RealCohesion.CrispRationals). If
F x < G x at some point x, then G - F is positive at x, hence at a
rational point by rational detection in n variables (gate G16), where
it is 0. So neither F x < G x nor G x < F x, and F x = G x. Equal crisp
functions are equal as elements of ♭ (ℝⁿ → ℝ), because the counit is
left cancellable on crisp sets.

The proof of the third part is that of gist.RealCohesion.FlatRealFunctions
for one variable, with the extension over rational boxes of
gist.RealCohesion.CrispExtensionOnBoxes in place of intervals. A crisp
continuous map extends to a crisp function, which agrees with it at
crisp points, so the map is the value of the extension. An arbitrary
map ♭ ℝⁿ → ♭ ℝ may be assumed crisp, because under Axiom R♭ maps into
♭ ℝ form a ♭-discrete type, given that ♭ ℝ is ♭-discrete (a consequence
of crisp induction, discharged in gist.RealCohesion.Theorems). The proof
of its continuity may then be assumed crisp too, because continuity of
a crisp map is a crisp proposition.

Since the consolidation of 13 November 2026, by Claude Opus 5.5 (W3 of
[3]), both parts are proved under Axiom C1 for an ordinary family of
pointed generators and the ♭-discreteness of 𝟚 (module under-C1): the
first part with a strictly rising generator path in ℝ, merely, which
gives the constancy of maps from ℝ to the finite chain quotient; the
third part without it, since maps into a ♭-discrete type form a
♭-discrete type and crisp propositions are ♭-discrete under C1 alone
(gist.RealCohesion.PunctualCohesion). Axiom R♭ is the case of the one
generator ℝ, whose identity map rises from 0 to 1, and the module under
Axiom R♭ keeps its names and types.

[1] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, revision of 12 November 2026, Theorem 3.3
    and Remark 7.18 (iii).
    references/C04-write-up-2026-11-12.tex

[2] Claude Fable 5.2. Second addendum to the formalization plan,
    revision 4 of 12 November 2026.
    references/F13b-second-addendum-rev4-as-amended.md

[3] Claude Fable 5.2. Plan: consolidation of r3, and "C1 + NC in place
    of R♭" (G27(d)), 13 November 2026, Section 4.3, as corrected by
    its addendum 01 and released by GPT-6 Astra.
    references/F02-consolidation-plan.md

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import gist.CohesiveApartness.Flat

module gist.RealCohesion.FlatFunctionsOfSeveralVariables
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
        (@♭ crisp-ap-^♭ : {@♭ 𝓤 : Universe} {@♭ A : 𝓤 ̇ } {@♭ x y : A}
                        → @♭ x ＝ y → x ^♭ ＝ y ^♭)
       where

open import Fin.Type using (Fin)
open import UF.Base using (happly)
open import UF.Sets
open import UF.Sets-Properties using (Π-is-set)
open import UF.Subsingletons-FunExt using (Π-is-prop)
open import Notation.Order
open import Rationals.Type
open import Rationals.Order
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import gist.RealCohesion.RationalPoints fe pe pt
open import gist.RealCohesion.RealLattice fe pe pt
 using (<-from-difference ; <-gives-positive-difference) renaming
  (_+_ to _ℝ+_ ; -_ to ℝ-_)
open import gist.RealCohesion.CrispRationals
 using (ℚ-has-crisp-representatives ; Fin-functions-have-crisp-representatives ;
         crisp-elim)
open import gist.RealCohesion.CrispExactIVT fe pe pt using (ℝ<-tight)
open import gist.RealCohesion.FiniteChainQuotient fe pe pt using (Q)
open import gist.RealCohesion.FunctionalHitting fe pe pt
 using (rational-from-positive)
open import gist.RealCohesion.SequentialHitting fe pe pt
 using (positive-from-rational)
import gist.RealCohesion.FiniteChainDiscreteness fe pe pt crisp-ap-^♭ as FCD
import gist.RealCohesion.RationalDetection fe pe pt as RD
import gist.RealCohesion.CrispExtensionOnBoxes fe pe pt as EB
open import gist.RealCohesion.ShulmanWeakeningsStatements fe pe pt
 using (is-♭-continuous)
import gist.RealCohesion.FlatRealFunctions fe pe pt crisp-ap-^♭ as FRF
open import gist.RealCohesion.Constancy fe pe pt
 using (Rising-Generator-Path ; identity-of-ℝ-rises)

open PropositionalTruncation pt

\end{code}

The canonical map, as in gist.RealCohesion.ShulmanWeakeningsStatements,
and the fact that continuity in the sense of that module is a
proposition.

\begin{code}

♭-apply' : {@♭ n : ℕ} → ♭ ((Fin n → ℝ) → ℝ) → ♭ (Fin n → ℝ) → ♭ ℝ
♭-apply' (F ^♭) (x ^♭) = (F x) ^♭

being-♭-continuous-is-prop : {@♭ n : ℕ} (k : ♭ (Fin n → ℝ) → ♭ ℝ)
                           → is-prop (is-♭-continuous k)
being-♭-continuous-is-prop k =
 Π-is-prop fe (λ x → Π-is-prop fe (λ ε → Π-is-prop fe (λ _ → ∃-is-prop)))

\end{code}

Crisp functions that agree at crisp points are equal, if maps ℝ → Q
are constant.

\begin{code}

module _ (ν : (k : ℝ → Q) (u v : ℝ) → k u ＝ k v) where

 agreement-at-rational-points
  : (@♭ n : ℕ) (@♭ F G : (Fin n → ℝ) → ℝ)
  → ((@♭ x : Fin n → ℝ) → F x ＝ G x)
  → (q : Fin n → ℚ) → F (λ i → ιₐ (q i)) ＝ G (λ i → ιₐ (q i))
 agreement-at-rational-points n F G k =
  crisp-elim (Fin-functions-have-crisp-representatives fe n 0ℚ
               ℚ-has-crisp-representatives)
   (λ q → F (λ i → ιₐ (q i)) ＝ G (λ i → ιₐ (q i)))
   (λ q₀ → k (λ i → ιₐ (q₀ i)))

 not-below-where-crisp-points-agree
  : (@♭ n : ℕ) (@♭ F G : (Fin n → ℝ) → ℝ)
  → ((@♭ x : Fin n → ℝ) → F x ＝ G x)
  → (x : Fin n → ℝ) → ¬ (F x < G x)
 not-below-where-crisp-points-agree n F G k x l =
  ∥∥-rec 𝟘-is-prop γ
   (RD.rational-detection-in-dimension ν n (λ y → G y ℝ+ (ℝ- F y)) x
     (rational-from-positive (G x ℝ+ (ℝ- F x))
       (<-gives-positive-difference (G x) (F x) l)))
  where
   γ : (Σ q ꞉ (Fin n → ℚ) , 0ℚ < G (λ i → ιₐ (q i)) ℝ+ (ℝ- F (λ i → ιₐ (q i))))
     → 𝟘
   γ (q , o) = <ℝ-irreflexive (G (λ i → ιₐ (q i)))
                (transport (_< G (λ i → ιₐ (q i)))
                  (agreement-at-rational-points n F G k q)
                  (<-from-difference (G (λ i → ιₐ (q i))) (F (λ i → ιₐ (q i)))
                    (positive-from-rational
                      (G (λ i → ιₐ (q i)) ℝ+ (ℝ- F (λ i → ιₐ (q i)))) o)))

 crisp-functions-agreeing-at-crisp-points-are-equal'
  : (@♭ n : ℕ) (@♭ F G : (Fin n → ℝ) → ℝ)
  → ((@♭ x : Fin n → ℝ) → F x ＝ G x) → F ＝ G
 crisp-functions-agreeing-at-crisp-points-are-equal' n F G k =
  dfunext fe
   (λ x → ℝ<-tight (F x) (G x) (not-below-where-crisp-points-agree n F G k x)
                                (not-below-where-crisp-points-agree n G F k' x))
  where
   k' : (@♭ x : Fin n → ℝ) → G x ＝ F x
   k' x = k x ⁻¹

\end{code}

From now on we assume Axiom C1 for an ordinary family of generators
and the ♭-discreteness of 𝟚, and for the first part also a strictly
rising generator path in ℝ, merely (gist.RealCohesion.Constancy),
which gives the constancy of maps ℝ → Q
(gist.RealCohesion.FiniteChainDiscreteness). Axiom R♭ is the case of
the one generator ℝ, below, with the names and types of the module
before the consolidation of 13 November 2026.

\begin{code}

module under-C1 {𝓥 𝓦 : Universe} {J : 𝓥 ̇ } (R : J → 𝓦 ̇ ) (c1 : Axiom-C1 R)
                (𝟚-is-♭-discrete : is-♭-discrete 𝟚)
              where

 private
  module FC = FCD.under-C1 R c1 𝟚-is-♭-discrete

 module _ (nc : ∥ Rising-Generator-Path R ∥) where

  ♭-apply-is-injective' : {@♭ n : ℕ} (F G : ♭ ((Fin n → ℝ) → ℝ))
                        → ♭-apply' F ＝ ♭-apply' G → F ＝ G
  ♭-apply-is-injective' {n} (F ^♭) (G ^♭) e =
   FC.♭-counit-is-lc-on-crisp-sets ((Fin n → ℝ) → ℝ)
    (Π-is-set fe (λ _ → ℝ-is-set))
    (crisp-functions-agreeing-at-crisp-points-are-equal'
      (FC.constancy-from-C1-and-NC nc) n F G agree)
   where
    agree : (@♭ x : Fin n → ℝ) → F x ＝ G x
    agree x = ap ♭-counit (happly e (x ^♭))

\end{code}

The third part (gate G21): every continuous map is a value, from crisp
excluded middle for 𝓤₀. Here we also assume that ♭ ℝ is ♭-discrete;
this part does not use the rising path.

\begin{code}

 module _ (♭ℝ-is-♭-discrete : is-♭-discrete (♭ ℝ)) where

  extension-is-a-value
   : (@♭ cem : Crisp-EM 𝓤₀) {@♭ n : ℕ} (@♭ k : ♭ (Fin n → ℝ) → ♭ ℝ)
     (@♭ c : is-♭-continuous k)
   → ♭-apply' ((EB.extension-on-boxes.extension cem k c) ^♭) ＝ k
  extension-is-a-value cem {n} k c = dfunext fe γ
   where
    γ : (y : ♭ (Fin n → ℝ))
      → ♭-apply' ((EB.extension-on-boxes.extension cem k c) ^♭) y ＝ k y
    γ (x ^♭) = FC.♭-counit-is-lc-on-crisp-sets ℝ ℝ-is-set
                (EB.extension-on-boxes.extension-agrees cem k c x)

  continuous-maps-are-values'
   : (@♭ cem : Crisp-EM 𝓤₀) {@♭ n : ℕ} (h : ♭ (Fin n → ℝ) → ♭ ℝ)
   → is-♭-continuous h
   → Σ F ꞉ ♭ ((Fin n → ℝ) → ℝ) , ♭-apply' F ＝ h
  continuous-maps-are-values' cem {n} h c =
   γ (pr₁ (pr₁ maps-are-♭-discrete) h) (pr₂ (pr₁ maps-are-♭-discrete) h)
   where
    maps-are-♭-discrete : is-♭-discrete (♭ (Fin n → ℝ) → ♭ ℝ)
    maps-are-♭-discrete =
     FRF.under-C1.maps-into-♭ℝ-are-♭-discrete R c1 𝟚-is-♭-discrete
      ♭ℝ-is-♭-discrete (♭ (Fin n → ℝ))

    γ : (w : ♭ (♭ (Fin n → ℝ) → ♭ ℝ)) → ♭-counit w ＝ h
      → Σ F ꞉ ♭ ((Fin n → ℝ) → ℝ) , ♭-apply' F ＝ h
    γ (k ^♭) e = δ (pr₁ (pr₁ (FC.crisp-props-are-♭-discrete
                                (is-♭-continuous k)
                                 (being-♭-continuous-is-prop k)))
                    (transport is-♭-continuous (e ⁻¹) c))
     where
      δ : ♭ (is-♭-continuous k) → Σ F ꞉ ♭ ((Fin n → ℝ) → ℝ) , ♭-apply' F ＝ h
      δ (c₀ ^♭) = (EB.extension-on-boxes.extension cem k c₀) ^♭ ,
                  (extension-is-a-value cem k c₀ ∙ e)

\end{code}

Under Axiom R♭, the instance for the one generator ℝ, with the names
and types of the module before the consolidation of 13 November 2026.

\begin{code}

module _ (r♭ : Singly-Generated-Punctual-Cohesion ℝ 0ℝ)
         (𝟚-is-♭-discrete : is-♭-discrete 𝟚)
       where

 private
  module I = under-C1 (λ (_ : 𝟙 {𝓤₀}) → ℝ)
              (singly-generated-punctual-cohesion-gives-Axiom-C1 fe ℝ 0ℝ r♭)
              𝟚-is-♭-discrete

 ♭-apply-is-injective' : {@♭ n : ℕ} (F G : ♭ ((Fin n → ℝ) → ℝ))
                       → ♭-apply' F ＝ ♭-apply' G → F ＝ G
 ♭-apply-is-injective' = I.♭-apply-is-injective' identity-of-ℝ-rises

 module _ (♭ℝ-is-♭-discrete : is-♭-discrete (♭ ℝ)) where

  extension-is-a-value
   : (@♭ cem : Crisp-EM 𝓤₀) {@♭ n : ℕ} (@♭ k : ♭ (Fin n → ℝ) → ♭ ℝ)
     (@♭ c : is-♭-continuous k)
   → ♭-apply' ((EB.extension-on-boxes.extension cem k c) ^♭) ＝ k
  extension-is-a-value = I.extension-is-a-value ♭ℝ-is-♭-discrete

  continuous-maps-are-values'
   : (@♭ cem : Crisp-EM 𝓤₀) {@♭ n : ℕ} (h : ♭ (Fin n → ℝ) → ♭ ℝ)
   → is-♭-continuous h
   → Σ F ꞉ ♭ ((Fin n → ℝ) → ℝ) , ♭-apply' F ＝ h
  continuous-maps-are-values' = I.continuous-maps-are-values' ♭ℝ-is-♭-discrete

\end{code}
