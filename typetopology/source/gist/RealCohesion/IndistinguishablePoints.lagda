Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. See the AI disclosure in
gist.RealCohesion.index.

Points that no map to 𝟚 separates, from Axiom R♭: Lemma 7.13 of the
write-up [1], for subsets of the whole line. Part of gate G23 of
Claude Fable 5.2's second addendum [2].

The exact statement. Lemma 7.13 of [1]: assume Axiom R♭; let a :: ℝ be
crisp, H the half-line [a, ∞), and U and V crisp subsets of H with
U ∪ V = H and a ∈ U. If V has a point, then there is y ∈ U ∩ V such
that q y = q a for every q : U → 𝟚. The same holds for (-∞, a].

The formal statement, indistinguishable-point, is that lemma for crisp
subsets U and V of ℝ in place of subsets of H, with a not necessarily
crisp. The half-line form follows by pulling U and V back along
x ↦ max x a, which maps ℝ onto H and fixes the points of H. Theorem
7.14 does not need it: gist.RealCohesion.CrispFunctionsAreContinuous
applies the lemma to two covers of ℝ, each by a set and a half-line.

The proof is that of [1], which is Fable's [3], audited by GPT-6
Astra [4], with two simplifications.

 * The double dual D X = (X → 𝟚) → 𝟚 takes the place of the image C X
   of the evaluation map X → D X. The proof needs only a ♭-discrete
   set that receives the evaluations.

 * S is the quotient of D U + D V by the relation E of [1] itself:
   w E w' if w = w', or if both w and w' come from points of U ∩ V. It
   is an equivalence relation, as [1] notes, and the relations of the
   set-pushout are among its instances, so the pushout is not needed.

The steps:

 1. Maps ℝ → 𝟚 are constant, so maps ℝ → D X are, and D X is
    ♭-discrete for crisp X, by the converse half of the axiom. So
    D U + D V has crisp representatives.

 2. S is a crisp set, so the counit ♭ S → S is an embedding; and every
    element of S is merely the class of an element of D U + D V, which
    is the counit of a crisp element. So S is ♭-discrete, as the
    quotient Q is in gist.RealCohesion.FiniteChainDiscreteness, and
    maps ℝ → S are constant by the forward half of the axiom.

 3. Λ s is the class of the evaluation at s in D U if s ∈ U, and in
    D V if s ∈ V. On U ∩ V the two classes agree, by E. So Λ : ℝ → S
    is defined by unique existence, without choice.

 4. Λ a = Λ b, so by effectiveness the classes of the evaluations at a
    in D U and at b in D V are related by E. They are not equal, so
    the first comes from a point y of U ∩ V: its evaluation in D U is
    that of a.

The quotient is defined before Axiom R♭ is assumed, from crisp data
only, so that it is crisp.

Since the consolidation of 13 November 2026, by Claude Opus 5.5 (W3 of
[5]), the steps are carried out under Axiom C1 for an ordinary family
of pointed generators and the ♭-discreteness of 𝟚 (modules
duals-under-C1 and quotient-under-C1). In step 1, D X is ♭-discrete as
a type of maps into the ♭-discrete type 𝟚
(gist.RealCohesion.PunctualCohesion), and in step 2, S is ♭-discrete as
before; neither uses more than C1. In step 2, maps ℝ → S are constant
if some map from a generator to ℝ rises strictly, merely, by the
transfer lemma for sets of gist.RealCohesion.Constancy, at the universe
𝓤₂ of S; steps 3 and 4 are unchanged. Axiom R♭ is the case of the one
generator ℝ, whose identity map rises from 0 to 1, and the module under
Axiom R♭ keeps its names and types.

[1] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, revision of 12 November 2026, Lemma 7.13.
    references/C04-write-up-2026-11-12.tex

[2] Claude Fable 5.2. Second addendum to the formalization plan,
    revision 4 of 12 November 2026.
    references/F13b-second-addendum-rev4-as-amended.md

[3] Claude Fable 5.2. Shulman's Theorem 11.5 from R♭ alone. Note of
    12 November 2026, Section 3, Lemma 2.
    references/F12-shulman-11-5.md

[4] GPT-6 Astra. Audit: Shulman 11.5 from R-flat alone, 12 November
    2026, Sections 2 and 3.
    references/A12-shulman-11-5-audit.txt

[5] Claude Fable 5.2. Plan: consolidation of r3, and "C1 + NC in place
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

module gist.RealCohesion.IndistinguishablePoints
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
        (@♭ crisp-ap-^♭ : {@♭ 𝓤 : Universe} {@♭ A : 𝓤 ̇ } {@♭ x y : A}
                        → @♭ x ＝ y → x ^♭ ＝ y ^♭)
       where

open import MLTT.Plus-Properties using (inl-lc ; +disjoint)
open import UF.Base using (happly)
open import UF.ImageAndSurjection pt
open import UF.Sets
open import UF.Subsingletons-FunExt using (Π-is-prop)
open import Quotient.Type using (EqRel)
open import Quotient.Large pt fe pe using (module large-quotient)
open import DedekindReals.Type fe pe pt
open import gist.RealCohesion.CrispRationals
 using (has-crisp-representatives ; +-has-crisp-representatives ;
        ♭-discrete-types-have-crisp-representatives)
import gist.RealCohesion.FiniteChainDiscreteness fe pe pt crisp-ap-^♭ as FCD
import gist.RealCohesion.PunctualCohesion fe as PC
open import gist.RealCohesion.Constancy fe pe pt
 using (Rising-Generator-Path ; identity-of-ℝ-rises ; module transfer)

open PropositionalTruncation pt

\end{code}

Double duals and evaluation.

\begin{code}

D : {𝓥 : Universe} → 𝓥 ̇ → 𝓥 ̇
D X = (X → 𝟚) → 𝟚

evaluation : {𝓥 : Universe} (X : 𝓥 ̇ ) → X → D X
evaluation X x q = q x

\end{code}

The quotient S for crisp U and V.

\begin{code}

module quotient (@♭ U V : ℝ → 𝓤₀ ̇ ) where

 𝕌 𝕍 : 𝓤₁ ̇
 𝕌 = Σ s ꞉ ℝ , U s
 𝕍 = Σ s ꞉ ℝ , V s

 W : 𝓤₁ ̇
 W = D 𝕌 ∔ D 𝕍

 from-the-overlap : W → 𝓤₁ ̇
 from-the-overlap w = ∃ (s , u , v) ꞉ (Σ s ꞉ ℝ , U s × V s) ,
                        (w ＝ inl (evaluation 𝕌 (s , u)))
                      ∔ (w ＝ inr (evaluation 𝕍 (s , v)))

 _≈_ : W → W → 𝓤₁ ̇
 w ≈ w' = (w ＝ w') ∨ (from-the-overlap w × from-the-overlap w')

 ≈-is-symmetric : symmetric _≈_
 ≈-is-symmetric w w' = ∥∥-functor γ
  where
   γ : (w ＝ w') ∔ (from-the-overlap w × from-the-overlap w')
     → (w' ＝ w) ∔ (from-the-overlap w' × from-the-overlap w)
   γ (inl e)        = inl (e ⁻¹)
   γ (inr (j , j')) = inr (j' , j)

 ≈-is-transitive : transitive _≈_
 ≈-is-transitive w w' w'' = ∥∥-rec (Π-is-prop fe (λ _ → ∨-is-prop))
                             (λ c → ∥∥-functor (γ c))
  where
   γ : (w ＝ w') ∔ (from-the-overlap w × from-the-overlap w')
     → (w' ＝ w'') ∔ (from-the-overlap w' × from-the-overlap w'')
     → (w ＝ w'') ∔ (from-the-overlap w × from-the-overlap w'')
   γ (inl e)        (inl e')        = inl (e ∙ e')
   γ (inl e)        (inr (j , j'')) =
    inr (transport from-the-overlap (e ⁻¹) j , j'')
   γ (inr (j , j')) (inl e')        = inr (j , transport from-the-overlap e' j')
   γ (inr (j , _))  (inr (_ , j'')) = inr (j , j'')

 relation : EqRel {𝓤₁} {𝓤₁} W
 relation = _≈_ , (λ w w' → ∨-is-prop) , (λ w → ∣ inl refl ∣) ,
            ≈-is-symmetric , ≈-is-transitive

 private
  module LQ = large-quotient W relation

 S : 𝓤₂ ̇
 S = LQ.X/≈

 [_] : W → S
 [_] = LQ.η

 S-is-set : is-set S
 S-is-set = LQ.X/≈-is-set

 S-induction : {𝓦 : Universe} (P : S → 𝓦 ̇ )
             → ((σ : S) → is-prop (P σ))
             → ((w : W) → P [ w ])
             → (σ : S) → P σ
 S-induction = LQ.quotient-induction

 related-points-have-the-same-class : {w w' : W} → w ≈ w' → [ w ] ＝ [ w' ]
 related-points-have-the-same-class = LQ.η-identifies-related-points

 points-with-the-same-class-are-related : {w w' : W} → [ w ] ＝ [ w' ] → w ≈ w'
 points-with-the-same-class-are-related = LQ.η-relates-identified-points

\end{code}

From now on we assume Axiom C1 for an ordinary family of generators,
an ordinary hypothesis, and that 𝟚 is ♭-discrete; Axiom R♭ is the
case of the one generator ℝ, below. Step 1: D X is ♭-discrete, as a
type of maps into the ♭-discrete type 𝟚
(gist.RealCohesion.PunctualCohesion).

\begin{code}

module duals-under-C1 {𝓥 𝓦 : Universe} {J : 𝓥 ̇ } (R : J → 𝓦 ̇ )
                      (c1 : Axiom-C1 R) (𝟚-is-♭-discrete : is-♭-discrete 𝟚)
                    where

 duals-are-♭-discrete : {@♭ 𝓣 : Universe} (@♭ X : 𝓣 ̇ ) → is-♭-discrete (D X)
 duals-are-♭-discrete X =
  PC.maps-into-♭-discrete-types-are-♭-discrete R c1 (X → 𝟚) 𝟚 𝟚-is-♭-discrete

module _ (r♭ : Singly-Generated-Punctual-Cohesion ℝ 0ℝ)
         (𝟚-is-♭-discrete : is-♭-discrete 𝟚)
       where

 duals-are-♭-discrete : {@♭ 𝓥 : Universe} (@♭ X : 𝓥 ̇ ) → is-♭-discrete (D X)
 duals-are-♭-discrete =
  duals-under-C1.duals-are-♭-discrete (λ (_ : 𝟙 {𝓤₀}) → ℝ)
   (singly-generated-punctual-cohesion-gives-Axiom-C1 fe ℝ 0ℝ r♭)
   𝟚-is-♭-discrete

\end{code}

For crisp U and V. The names of the quotient are opened before Axiom
R♭ is assumed, so that they do not depend on it and stay crisp.

\begin{code}

module _ (@♭ U V : ℝ → 𝓤₀ ̇ ) where

 open quotient U V

 module quotient-under-C1 {𝓥 𝓦 : Universe} {J : 𝓥 ̇ } (R : J → 𝓦 ̇ )
                          (c1 : Axiom-C1 R)
                          (𝟚-is-♭-discrete : is-♭-discrete 𝟚)
                        where

  open Axiom-C1 c1

  W-has-crisp-representatives : has-crisp-representatives W
  W-has-crisp-representatives =
   +-has-crisp-representatives
    (♭-discrete-types-have-crisp-representatives
      (duals-under-C1.duals-are-♭-discrete R c1 𝟚-is-♭-discrete 𝕌))
    (♭-discrete-types-have-crisp-representatives
      (duals-under-C1.duals-are-♭-discrete R c1 𝟚-is-♭-discrete 𝕍))

\end{code}

Step 2.

\begin{code}

  ♭-counit-of-S-is-surjection : is-surjection (♭-counit {𝓤₂} {S})
  ♭-counit-of-S-is-surjection =
   S-induction (λ σ → ∃ t ꞉ ♭ S , ♭-counit t ＝ σ) (λ σ → ∃-is-prop) I
   where
    I : (w : W) → ∃ t ꞉ ♭ S , ♭-counit t ＝ [ w ]
    I w = ∣ γ (W-has-crisp-representatives w) ∣
     where
      γ : (Σ c ꞉ ♭ W , ♭-counit c ＝ w) → Σ t ꞉ ♭ S , ♭-counit t ＝ [ w ]
      γ ((w' ^♭) , e) = ([ w' ] ^♭) , ap [_] e

  S-is-♭-discrete : is-♭-discrete S
  S-is-♭-discrete = surjective-embeddings-are-equivs ♭-counit
                     (FCD.under-C1.♭-counit-is-embedding-on-crisp-sets R c1
                       𝟚-is-♭-discrete S S-is-set)
                     ♭-counit-of-S-is-surjection

  generator-maps-to-S-are-constant
   : (j : J) (h : R j → S) (r : R j) → h r ＝ h (base-point j)
  generator-maps-to-S-are-constant =
   PC.generator-maps-are-constant R c1 S S-is-♭-discrete

\end{code}

Maps from ℝ to S are constant, from a strictly rising generator path,
by the transfer lemma for sets of gist.RealCohesion.Constancy, at the
set S, which lives in 𝓤₂; the truncation of the path is eliminated
into an identity type of the set S.

\begin{code}

  module _ (nc : ∥ Rising-Generator-Path R ∥) where

   maps-from-ℝ-to-S-are-constant : (h : ℝ → S) (u v : ℝ) → h u ＝ h v
   maps-from-ℝ-to-S-are-constant h u v = ∥∥-rec S-is-set γ nc
    where
     γ : Rising-Generator-Path R → h u ＝ h v
     γ (j , g , x , y , l) =
      transfer.constancy-transfers-along-a-strict-rise (base-point j) S-is-set
       (generator-maps-to-S-are-constant j) g x y h l u v

\end{code}

Steps 3 and 4.

\begin{code}

   indistinguishable-point
    : ((s : ℝ) → is-prop (U s))
    → ((s : ℝ) → is-prop (V s))
    → ((s : ℝ) → U s ∨ V s)
    → (a : ℝ) (u : U a) (b : ℝ) → V b
    → ∃ y ꞉ ℝ , Σ w ꞉ U y , V y × ((q : 𝕌 → 𝟚) → q (y , w) ＝ q (a , u))
   indistinguishable-point U-is-prop V-is-prop cover a u b v =
    ∥∥-rec ∃-is-prop γ (points-with-the-same-class-are-related I)
    where
     class-in-U : (s : ℝ) → U s → S
     class-in-U s w = [ inl (evaluation 𝕌 (s , w)) ]

     class-in-V : (s : ℝ) → V s → S
     class-in-V s w = [ inr (evaluation 𝕍 (s , w)) ]

     classes-agree : (s : ℝ) (w : U s) (w' : V s)
                   → class-in-U s w ＝ class-in-V s w'
     classes-agree s w w' =
      related-points-have-the-same-class
       ∣ inr (∣ (s , w , w') , inl refl ∣ , ∣ (s , w , w') , inr refl ∣) ∣

     Value : ℝ → 𝓤₂ ̇
     Value s = Σ σ ꞉ S , ((w : U s) → σ ＝ class-in-U s w)
                       × ((w : V s) → σ ＝ class-in-V s w)

     Value-is-prop : (s : ℝ) → is-prop (Value s)
     Value-is-prop s (σ , f , g) (σ' , f' , g') =
      to-subtype-＝ (λ τ → ×-is-prop (Π-is-prop fe (λ _ → S-is-set))
                                     (Π-is-prop fe (λ _ → S-is-set)))
       (∥∥-rec S-is-set δ (cover s))
      where
       δ : U s ∔ V s → σ ＝ σ'
       δ (inl w) = f w ∙ f' w ⁻¹
       δ (inr w) = g w ∙ g' w ⁻¹

     value : (s : ℝ) → Value s
     value s = ∥∥-rec (Value-is-prop s) δ (cover s)
      where
       δ : U s ∔ V s → Value s
       δ (inl w) = class-in-U s w ,
                   (λ w' → ap (class-in-U s) (U-is-prop s w w')) ,
                   classes-agree s w
       δ (inr w) = class-in-V s w ,
                   (λ w' → classes-agree s w' w ⁻¹) ,
                   (λ w' → ap (class-in-V s) (V-is-prop s w w'))

     Λ : ℝ → S
     Λ s = pr₁ (value s)

     I : [ inl (evaluation 𝕌 (a , u)) ] ＝ [ inr (evaluation 𝕍 (b , v)) ]
     I = pr₁ (pr₂ (value a)) u ⁻¹
       ∙ maps-from-ℝ-to-S-are-constant Λ a b
       ∙ pr₂ (pr₂ (value b)) v

     γ : (inl (evaluation 𝕌 (a , u)) ＝ inr (evaluation 𝕍 (b , v)))
       ∔ (from-the-overlap (inl (evaluation 𝕌 (a , u)))
           × from-the-overlap (inr (evaluation 𝕍 (b , v))))
       → ∃ y ꞉ ℝ , Σ w ꞉ U y , V y × ((q : 𝕌 → 𝟚) → q (y , w) ＝ q (a , u))
     γ (inl e)       = 𝟘-elim (+disjoint e)
     γ (inr (j , _)) = ∥∥-functor δ j
      where
       δ : (Σ (s , w , w') ꞉ (Σ s ꞉ ℝ , U s × V s) ,
              (inl (evaluation 𝕌 (a , u)) ＝ inl (evaluation 𝕌 (s , w)))
            ∔ (inl (evaluation 𝕌 (a , u)) ＝ inr (evaluation 𝕍 (s , w'))))
         → Σ y ꞉ ℝ , Σ w ꞉ U y , V y × ((q : 𝕌 → 𝟚) → q (y , w) ＝ q (a , u))
       δ ((s , w , w') , inl e) = s , w , w' , (λ q → happly (inl-lc e) q ⁻¹)
       δ ((s , w , w') , inr e) = 𝟘-elim (+disjoint e)

\end{code}

Under Axiom R♭: the instance for the one generator ℝ, whose identity
map rises from 0 to 1, with the names and types of the module before
the consolidation of 13 November 2026.

\begin{code}

 module _ (r♭ : Singly-Generated-Punctual-Cohesion ℝ 0ℝ)
          (𝟚-is-♭-discrete : is-♭-discrete 𝟚)
        where

  private
   module G = quotient-under-C1 (λ (_ : 𝟙 {𝓤₀}) → ℝ)
               (singly-generated-punctual-cohesion-gives-Axiom-C1 fe ℝ 0ℝ r♭)
               𝟚-is-♭-discrete

  W-has-crisp-representatives : has-crisp-representatives W
  W-has-crisp-representatives = G.W-has-crisp-representatives

  ♭-counit-of-S-is-surjection : is-surjection (♭-counit {𝓤₂} {S})
  ♭-counit-of-S-is-surjection = G.♭-counit-of-S-is-surjection

  S-is-♭-discrete : is-♭-discrete S
  S-is-♭-discrete = G.S-is-♭-discrete

  maps-from-ℝ-to-S-are-constant : (h : ℝ → S) (u v : ℝ) → h u ＝ h v
  maps-from-ℝ-to-S-are-constant =
   G.maps-from-ℝ-to-S-are-constant identity-of-ℝ-rises

  indistinguishable-point
   : ((s : ℝ) → is-prop (U s))
   → ((s : ℝ) → is-prop (V s))
   → ((s : ℝ) → U s ∨ V s)
   → (a : ℝ) (u : U a) (b : ℝ) → V b
   → ∃ y ꞉ ℝ , Σ w ꞉ U y , V y × ((q : 𝕌 → 𝟚) → q (y , w) ＝ q (a , u))
  indistinguishable-point = G.indistinguishable-point identity-of-ℝ-rises

\end{code}
