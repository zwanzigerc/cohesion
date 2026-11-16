Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 11 November 2026. See the AI disclosure in
gist.RealCohesion.index.

Shulman's Corollary 11.6 without Axiom T: the crisp functions ℝ → ℝ
are exactly the ε-δ continuous maps on the crisp reals.

Shulman's Corollary 11.6 [1] says, under Axioms LEM, R♭ and T, that
the canonical map

  ♭ (ℝ → ℝ) → (♭ ℝ → ♭ ℝ)

is injective, with image the ε-δ continuous maps. Fable's note [2],
audited by GPT-6 Astra, observes that Shulman's proof uses Axiom T only
through his Theorem 11.5, so that, with Theorem 11.5 proved without
Axiom T, the corollary holds under LEM and R♭. We formalize the
corollary from crisp excluded middle and Axiom R♭, by a different
route in two places.

 * Injectivity, from Axiom R♭ alone. Shulman deduces it from the
   concreteness of ℝ [1, Theorem 8.20; 2], which is stated with the
   sharp modality ♯. We use GPT-6 Astra's rational detection
   (gist.RealCohesion.RationalDetection) instead: if crisp F and G
   agree at crisp points and F x < G x at some real x, rational
   detection gives a rational r with F r < G r, but rationals are
   crisp. So crisp functions that agree at crisp points are equal,
   and since F = G is a crisp proposition, it is ♭-discrete, which
   gives F ^♭ = G ^♭. No ♯ is involved.

 * The image. The canonical map sends crisp functions to continuous
   maps by Theorem 11.5 without Axiom T at crisp points
   (gist.RealCohesion.CrispContinuity). Conversely, a crisp continuous
   map h extends to a crisp function ℝ → ℝ
   (gist.RealCohesion.CrispExtension), which agrees with h at crisp
   points. An arbitrary element of ♭ ℝ → ♭ ℝ may be assumed crisp,
   because under Axiom R♭ the type ♭ ℝ → ♭ ℝ is ♭-discrete: maps
   ℝ → ♭ ℝ are constant, so maps from ℝ to ♭ ℝ → ♭ ℝ are constant.
   This uses that ♭ ℝ is ♭-discrete, a consequence of crisp induction
   proved in gist.RealCohesion.FlatSplit, and taken here as a
   hypothesis. Likewise the proof of continuity may be assumed crisp,
   because continuity of a crisp map is a crisp proposition.

We also obtain the equivalence of ♭ (ℝ → ℝ) with the type of ε-δ
continuous maps ♭ ℝ → ♭ ℝ.

Fable's note and the write-up [3, Theorem 3.3] state the same for
functions of n variables. That version is not formalized here.

Since the consolidation of 13 November 2026, by Claude Opus 5.5 (W3 of
[4]), the corollary is proved under Axiom C1 for an ordinary family of
pointed generators and the ♭-discreteness of 𝟚 (module under-C1).
Injectivity, and that the canonical map lands in the continuous maps,
use a strictly rising generator path in ℝ, merely, which gives the
constancy of maps from ℝ to the finite chain quotient; that every
continuous map is in the image does not, since under C1 maps into the
♭-discrete type ♭ ℝ form a ♭-discrete type and crisp propositions are
♭-discrete (gist.RealCohesion.PunctualCohesion). Maps from ℝ to ♭ ℝ are
constant by the transfer lemma for sets of gist.RealCohesion.Constancy,
♭ ℝ being a set because the counit is left cancellable on crisp sets.
Axiom R♭ is the case of the one generator ℝ, whose identity map rises
from 0 to 1, and the module under Axiom R♭ keeps its names and types.

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3

[2] Fable. Shulman's stated questions: three updates, Part A.4.
    Working note, 10 November 2026, audited by GPT-6 Astra.
    references/F18-shulman-three-updates.md

[3] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, revised 10 November 2026.
    references/C02-write-up-2026-11-10.tex

[4] Claude Fable 5.2. Plan: consolidation of r3, and "C1 + NC in place
    of R♭" (G27(d)), 13 November 2026, Section 4.3, as corrected by
    its addendum 01 and released by GPT-6 Astra.
    references/F02-consolidation-plan.md

\begin{code}

{-# OPTIONS --safe --without-K --cohesion --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import gist.CohesiveApartness.Flat

module gist.RealCohesion.FlatRealFunctions
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
        (@♭ crisp-ap-^♭ : {@♭ 𝓤 : Universe} {@♭ A : 𝓤 ̇ } {@♭ x y : A}
                        → @♭ x ＝ y → x ^♭ ＝ y ^♭)
       where

open import Notation.CanonicalMap
open import Notation.Order
open import UF.Base
open import UF.Embeddings
open import UF.Equiv
open import UF.LeftCancellable
open import UF.Sets
open import UF.Sets-Properties
open import Rationals.Type
open import Rationals.Order
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import Rationals.Positive using (ℚ₊)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import DedekindReals.Properties fe pe pt using (ℝ-arithmetically-located)
open import MetricSpaces.DedekindReals fe pe pt using (B-ℝ)
open import gist.RealCohesion.RationalPoints fe pe pt
open import gist.RealCohesion.RealOrder fe pe pt using (not-below-and-above)
open import gist.RealCohesion.RealBalls fe pe pt
open import gist.RealCohesion.CrispRationals
 using (ℚ-has-crisp-representatives ; crisp-elim)
open import gist.RealCohesion.FiniteChainQuotient fe pe pt using (Q)
open import gist.RealCohesion.FiniteChainDiscreteness fe pe pt crisp-ap-^♭
 using (maps-from-ℝ-to-Q-are-constant ; crisp-props-are-♭-discrete ;
        ♭-counit-is-lc-on-crisp-sets)
import gist.RealCohesion.FiniteChainDiscreteness fe pe pt crisp-ap-^♭ as FCD
import gist.RealCohesion.PunctualCohesion fe as PC
open import gist.RealCohesion.Constancy fe pe pt
 using (Rising-Generator-Path ; identity-of-ℝ-rises ; module transfer)
open import gist.RealCohesion.RationalDetection fe pe pt
 using (rational-detection-window₂)
open import gist.RealCohesion.CrispExactIVT fe pe pt using (ℝ<-tight)
open import gist.RealCohesion.CrispContinuity fe pe pt
 using (crisp-real-continuity)
open import gist.RealCohesion.CrispUniformContinuity fe pe pt
 using (is-ε-δ-continuous ; being-ε-δ-continuous-is-prop)
import gist.RealCohesion.CrispExtension fe pe pt as CE

open PropositionalTruncation pt

\end{code}

The canonical map.

\begin{code}

♭-action : {@♭ 𝓤 𝓥 : Universe} {@♭ A : 𝓤 ̇ } {@♭ B : 𝓥 ̇ }
         → ♭ (A → B) → ♭ A → ♭ B
♭-action (f ^♭) (x ^♭) = (f x) ^♭

\end{code}

Crisp functions are determined by their values at crisp points,
assuming that maps ℝ → Q are constant.

\begin{code}

module _ (ν : (k : ℝ → Q) (u v : ℝ) → k u ＝ k v) where

 agreement-at-rationals-is-contradicted
  : (@♭ F G : ℝ → ℝ) → ((@♭ x : ℝ) → F x ＝ G x) → (q u v : ℚ)
  → (Σ r ꞉ ℚ ,
      ((u < F (ιₐ r)) × (F (ιₐ r) < q)) × ((q < G (ιₐ r)) × (G (ιₐ r) < v)))
  → 𝟘 {𝓤₀}
 agreement-at-rationals-is-contradicted F G k q u v (r , (_ , a) , (b , _)) =
  not-below-and-above (F (ιₐ r)) q (transport (q <_) (agree ⁻¹) b) a
  where
   agree : F (ιₐ r) ＝ G (ιₐ r)
   agree = crisp-elim ℚ-has-crisp-representatives (λ r → F (ιₐ r) ＝ G (ιₐ r))
            (λ r₀ → k (ιₐ r₀)) r

 not-below-where-crisp-points-agree
  : (@♭ F G : ℝ → ℝ) → ((@♭ x : ℝ) → F x ＝ G x) → (x : ℝ) → ¬ (F x < G x)
 not-below-where-crisp-points-agree F G k x l = ∥∥-rec 𝟘-is-prop γ l
  where
   γ : (Σ q ꞉ ℚ , (F x < q) × (q < G x)) → 𝟘
   γ (q , m , n) = ∥∥-rec 𝟘-is-prop δ
                    (binary-choice (inhabited-from-real-L (F x))
                      (inhabited-from-real-R (G x)))
    where
     δ : (Σ u ꞉ ℚ , u < F x) × (Σ v ꞉ ℚ , G x < v) → 𝟘
     δ ((u , o) , (v , o')) = ∥∥-rec 𝟘-is-prop
                               (agreement-at-rationals-is-contradicted F G k q u
                                 v)
                               (rational-detection-window₂ ν F G x u q q v o m n
                                 o')

 crisp-functions-agreeing-at-crisp-points-are-equal
  : (@♭ F G : ℝ → ℝ) → ((@♭ x : ℝ) → F x ＝ G x) → F ＝ G
 crisp-functions-agreeing-at-crisp-points-are-equal F G k =
  dfunext fe
   (λ x → ℝ<-tight (F x) (G x) (not-below-where-crisp-points-agree F G k x)
                                (not-below-where-crisp-points-agree G F k' x))
  where
   k' : (@♭ x : ℝ) → G x ＝ F x
   k' x = k x ⁻¹

\end{code}

From now on we assume Axiom C1 for an ordinary family of generators
and the ♭-discreteness of 𝟚; for the results that use the constancy of
maps ℝ → Q also a strictly rising generator path in ℝ, merely, which
gives it (gist.RealCohesion.FiniteChainDiscreteness). Axiom R♭ is the
case of the one generator ℝ, below, with the names and types of the
module before the consolidation of 13 November 2026.

\begin{code}

module under-C1 {𝓥 𝓦 : Universe} {J : 𝓥 ̇ } (R : J → 𝓦 ̇ ) (c1 : Axiom-C1 R)
                (𝟚-is-♭-discrete : is-♭-discrete 𝟚)
              where

 private
  module FC = FCD.under-C1 R c1 𝟚-is-♭-discrete

 open Axiom-C1 c1

 ♭ℝ-is-set : is-set (♭ ℝ)
 ♭ℝ-is-set = subtypes-of-sets-are-sets' ♭-counit
              (FC.♭-counit-is-lc-on-crisp-sets ℝ ℝ-is-set)
               ℝ-is-set

 continuity-from-interval
  : (@♭ F : ℝ → ℝ) (t : ℝ) (ε : ℚ) (l : 0ℚ < ε) (u v r r' : ℚ)
  → u < F t → F t < v → v ℚ- u < ε
  → ((@♭ s : ℝ) → r < s → s < r' → (u < F s) × (F s < v))
  → (Σ δ ꞉ ℚ , Ball-Inside r r' t δ)
  → Σ δ ꞉ ℚ₊ , ((y : ♭ ℝ) → B-ℝ (♭-counit y) t δ
                          → B-ℝ (♭-counit (♭-action (F ^♭) y)) (F t) (ε , l))
 continuity-from-interval F t ε l u v r r' a b w k (δ , m , f) = (δ , m) , γ
  where
   γ : (y : ♭ ℝ) → B-ℝ (♭-counit y) t (δ , m)
     → B-ℝ (♭-counit (♭-action (F ^♭) y)) (F t) (ε , l)
   γ (s ^♭) c = Close-from-interval ε u v (F s) (F t)
                 (pr₁ (k s (pr₁ (f s c)) (pr₂ (f s c))))
                 (pr₂ (k s (pr₁ (f s c)) (pr₂ (f s c))))
                 a b w

\end{code}

The results that use the constancy of maps ℝ → Q. The canonical map
lands in the continuous maps, by Theorem 11.5 at crisp points, which
uses crisp excluded middle.

\begin{code}

 module _ (nc : ∥ Rising-Generator-Path R ∥) where

  maps-from-ℝ-to-Q-are-constant' : (k : ℝ → Q) (u v : ℝ) → k u ＝ k v
  maps-from-ℝ-to-Q-are-constant' = FC.constancy-from-C1-and-NC nc

  ♭-action-is-left-cancellable : left-cancellable (♭-action {𝓤₁} {𝓤₁} {ℝ} {ℝ})
  ♭-action-is-left-cancellable {F ^♭} {G ^♭} e =
   FC.♭-counit-is-lc-on-crisp-sets (ℝ → ℝ)
    (Π-is-set fe (λ _ → ℝ-is-set))
    (crisp-functions-agreeing-at-crisp-points-are-equal
      maps-from-ℝ-to-Q-are-constant' F G agree)
   where
    agree : (@♭ x : ℝ) → F x ＝ G x
    agree x = ap ♭-counit (happly e (x ^♭))

  ♭-action-is-embedding : is-embedding (♭-action {𝓤₁} {𝓤₁} {ℝ} {ℝ})
  ♭-action-is-embedding = lc-maps-into-sets-are-embeddings ♭-action
                           ♭-action-is-left-cancellable
                            (Π-is-set fe (λ _ → ♭ℝ-is-set))

  crisp-functions-are-ε-δ-continuous
   : (@♭ cem : Crisp-EM 𝓤₁) (u : ♭ (ℝ → ℝ)) → is-ε-δ-continuous (♭-action u)
  crisp-functions-are-ε-δ-continuous cem (F ^♭) (t ^♭) (ε , l) =
   ∥∥-rec ∃-is-prop γ (ℝ-arithmetically-located (F t) (ε , l))
   where
    γ : (Σ (u , v) ꞉ ℚ × ℚ , (u < F t < v) × (v ℚ- u < ε))
      → ∃ δ ꞉ ℚ₊ , ((y : ♭ ℝ) → B-ℝ (♭-counit y) t δ
                              → B-ℝ (♭-counit (♭-action (F ^♭) y)) (F t)
                                 (ε , l))
    γ ((u , v) , (a , b) , w) =
     ∥∥-rec ∃-is-prop δ
      (crisp-real-continuity cem maps-from-ℝ-to-Q-are-constant' F t u v a b)
     where
      δ : (Σ (r , r') ꞉ ℚ × ℚ , (r < t) × (t < r')
                              × ((@♭ s : ℝ) → r < s → s < r'
                                 → (u < F s) × (F s < v)))
        → ∃ δ ꞉ ℚ₊ , ((y : ♭ ℝ) → B-ℝ (♭-counit y) t δ
                                → B-ℝ (♭-counit (♭-action (F ^♭) y)) (F t)
                                   (ε , l))
      δ ((r , r') , p , p' , k) =
       ∥∥-functor (continuity-from-interval F t ε l u v r r' a b w k)
        (ball-inside-interval r r' t p p')

  images-are-continuous
   : (@♭ cem : Crisp-EM 𝓤₁) (h : ♭ ℝ → ♭ ℝ) → fiber ♭-action h
   → is-ε-δ-continuous h
  images-are-continuous cem h (u , e) =
   transport is-ε-δ-continuous e (crisp-functions-are-ε-δ-continuous cem u)

\end{code}

Every continuous map is in the image. Here we also assume that ♭ ℝ is
♭-discrete. Then maps from any crisp type into ♭ ℝ form a ♭-discrete
type (gist.RealCohesion.PunctualCohesion), without NC;
gist.RealCohesion.FlatFunctionsOfSeveralVariables uses this for maps
on ♭ ℝⁿ.

\begin{code}

 module _ (♭ℝ-is-♭-discrete : is-♭-discrete (♭ ℝ)) where

  maps-into-♭ℝ-are-♭-discrete : {@♭ 𝓤 : Universe} (@♭ D : 𝓤 ̇ )
                              → is-♭-discrete (D → ♭ ℝ)
  maps-into-♭ℝ-are-♭-discrete D =
   PC.maps-into-♭-discrete-types-are-♭-discrete R c1 D (♭ ℝ) ♭ℝ-is-♭-discrete

  maps-on-♭ℝ-are-♭-discrete : is-♭-discrete (♭ ℝ → ♭ ℝ)
  maps-on-♭ℝ-are-♭-discrete = maps-into-♭ℝ-are-♭-discrete (♭ ℝ)

  extension-is-a-preimage
   : (@♭ cem : Crisp-EM 𝓤₁) (@♭ k : ♭ ℝ → ♭ ℝ) (@♭ c : is-ε-δ-continuous k)
   → ♭-action ((CE.extension.extension cem k c) ^♭) ＝ k
  extension-is-a-preimage cem k c = dfunext fe γ
   where
    γ : (y : ♭ ℝ) → ♭-action ((CE.extension.extension cem k c) ^♭) y ＝ k y
    γ (x ^♭) = FC.♭-counit-is-lc-on-crisp-sets ℝ ℝ-is-set
                (CE.extension.extension-agrees cem k c x)

  continuous-maps-are-images
   : (@♭ cem : Crisp-EM 𝓤₁) (h : ♭ ℝ → ♭ ℝ) → is-ε-δ-continuous h
   → fiber ♭-action h
  continuous-maps-are-images cem h c =
   γ (pr₁ (pr₁ maps-on-♭ℝ-are-♭-discrete) h)
    (pr₂ (pr₁ maps-on-♭ℝ-are-♭-discrete) h)
   where
    γ : (w : ♭ (♭ ℝ → ♭ ℝ)) → ♭-counit w ＝ h → fiber ♭-action h
    γ (k ^♭) e = δ (pr₁ (pr₁ (FC.crisp-props-are-♭-discrete
                                (is-ε-δ-continuous k)
                                 (being-ε-δ-continuous-is-prop k)))
                    (transport is-ε-δ-continuous (e ⁻¹) c))
     where
      δ : ♭ (is-ε-δ-continuous k) → fiber ♭-action h
      δ (c₀ ^♭) = (CE.extension.extension cem k c₀) ^♭ ,
                  (extension-is-a-preimage cem k c₀ ∙ e)

\end{code}

Maps from ℝ to the ♭-discrete set ♭ ℝ are constant, by the transfer
lemma for sets; and Shulman's Corollary 11.6 without Axiom T, and the
equivalence of ♭ (ℝ → ℝ) with the continuous maps.

\begin{code}

  module _ (nc : ∥ Rising-Generator-Path R ∥) where

   maps-from-ℝ-to-♭ℝ-are-constant : (f : ℝ → ♭ ℝ) (u v : ℝ) → f u ＝ f v
   maps-from-ℝ-to-♭ℝ-are-constant f u v = ∥∥-rec ♭ℝ-is-set γ nc
    where
     γ : Rising-Generator-Path R → f u ＝ f v
     γ (j , g , x , y , l) =
      transfer.constancy-transfers-along-a-strict-rise (base-point j)
       ♭ℝ-is-set
       (PC.generator-maps-are-constant R c1 (♭ ℝ) ♭ℝ-is-♭-discrete j)
       g x y f l u v

   Shulman-Corollary-11-6
    : (@♭ cem : Crisp-EM 𝓤₁)
    → is-embedding (♭-action {𝓤₁} {𝓤₁} {ℝ} {ℝ})
    × ((h : ♭ ℝ → ♭ ℝ) → fiber ♭-action h ↔ is-ε-δ-continuous h)
   Shulman-Corollary-11-6 cem =
    ♭-action-is-embedding nc ,
    (λ h → images-are-continuous nc cem h , continuous-maps-are-images cem h)

   crisp-functions-are-the-continuous-maps
    : (@♭ cem : Crisp-EM 𝓤₁)
    → ♭ (ℝ → ℝ) ≃ (Σ h ꞉ (♭ ℝ → ♭ ℝ) , is-ε-δ-continuous h)
   crisp-functions-are-the-continuous-maps cem = qinveq φ (ψ , ψφ , φψ)
    where
     φ : ♭ (ℝ → ℝ) → Σ h ꞉ (♭ ℝ → ♭ ℝ) , is-ε-δ-continuous h
     φ u = ♭-action u , crisp-functions-are-ε-δ-continuous nc cem u

     ψ : (Σ h ꞉ (♭ ℝ → ♭ ℝ) , is-ε-δ-continuous h) → ♭ (ℝ → ℝ)
     ψ (h , c) = pr₁ (continuous-maps-are-images cem h c)

     ψφ : ψ ∘ φ ∼ id
     ψφ u = ♭-action-is-left-cancellable nc
             (pr₂ (continuous-maps-are-images cem (♭-action u)
                    (crisp-functions-are-ε-δ-continuous nc cem u)))

     φψ : φ ∘ ψ ∼ id
     φψ (h , c) = to-subtype-＝ being-ε-δ-continuous-is-prop
                   (pr₂ (continuous-maps-are-images cem h c))

\end{code}

Under Axiom R♭, the instance for the one generator ℝ, whose identity
map rises from 0 to 1, with the names and types of the module before
the consolidation of 13 November 2026.

\begin{code}

module _ (r♭ : Singly-Generated-Punctual-Cohesion ℝ 0ℝ)
         (𝟚-is-♭-discrete : is-♭-discrete 𝟚)
       where

 private
  module G = under-C1 (λ (_ : 𝟙 {𝓤₀}) → ℝ)
              (singly-generated-punctual-cohesion-gives-Axiom-C1 fe ℝ 0ℝ r♭)
              𝟚-is-♭-discrete

 maps-from-ℝ-to-Q-are-constant' : (k : ℝ → Q) (u v : ℝ) → k u ＝ k v
 maps-from-ℝ-to-Q-are-constant' =
  maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete

 ♭ℝ-is-set : is-set (♭ ℝ)
 ♭ℝ-is-set = G.♭ℝ-is-set

 ♭-action-is-left-cancellable : left-cancellable (♭-action {𝓤₁} {𝓤₁} {ℝ} {ℝ})
 ♭-action-is-left-cancellable =
  G.♭-action-is-left-cancellable identity-of-ℝ-rises

 ♭-action-is-embedding : is-embedding (♭-action {𝓤₁} {𝓤₁} {ℝ} {ℝ})
 ♭-action-is-embedding = G.♭-action-is-embedding identity-of-ℝ-rises

 continuity-from-interval
  : (@♭ F : ℝ → ℝ) (t : ℝ) (ε : ℚ) (l : 0ℚ < ε) (u v r r' : ℚ)
  → u < F t → F t < v → v ℚ- u < ε
  → ((@♭ s : ℝ) → r < s → s < r' → (u < F s) × (F s < v))
  → (Σ δ ꞉ ℚ , Ball-Inside r r' t δ)
  → Σ δ ꞉ ℚ₊ , ((y : ♭ ℝ) → B-ℝ (♭-counit y) t δ
                          → B-ℝ (♭-counit (♭-action (F ^♭) y)) (F t) (ε , l))
 continuity-from-interval = G.continuity-from-interval

 crisp-functions-are-ε-δ-continuous
  : (@♭ cem : Crisp-EM 𝓤₁) (u : ♭ (ℝ → ℝ)) → is-ε-δ-continuous (♭-action u)
 crisp-functions-are-ε-δ-continuous =
  G.crisp-functions-are-ε-δ-continuous identity-of-ℝ-rises

 images-are-continuous
  : (@♭ cem : Crisp-EM 𝓤₁) (h : ♭ ℝ → ♭ ℝ) → fiber ♭-action h
  → is-ε-δ-continuous h
 images-are-continuous = G.images-are-continuous identity-of-ℝ-rises

 module _ (♭ℝ-is-♭-discrete : is-♭-discrete (♭ ℝ)) where

  maps-from-ℝ-to-♭ℝ-are-constant : (f : ℝ → ♭ ℝ) (r : ℝ) → f r ＝ f 0ℝ
  maps-from-ℝ-to-♭ℝ-are-constant f r =
   G.maps-from-ℝ-to-♭ℝ-are-constant ♭ℝ-is-♭-discrete identity-of-ℝ-rises f r 0ℝ

  maps-into-♭ℝ-are-♭-discrete : {@♭ 𝓤 : Universe} (@♭ D : 𝓤 ̇ )
                              → is-♭-discrete (D → ♭ ℝ)
  maps-into-♭ℝ-are-♭-discrete = G.maps-into-♭ℝ-are-♭-discrete ♭ℝ-is-♭-discrete

  maps-on-♭ℝ-are-♭-discrete : is-♭-discrete (♭ ℝ → ♭ ℝ)
  maps-on-♭ℝ-are-♭-discrete = G.maps-on-♭ℝ-are-♭-discrete ♭ℝ-is-♭-discrete

  extension-is-a-preimage
   : (@♭ cem : Crisp-EM 𝓤₁) (@♭ k : ♭ ℝ → ♭ ℝ) (@♭ c : is-ε-δ-continuous k)
   → ♭-action ((CE.extension.extension cem k c) ^♭) ＝ k
  extension-is-a-preimage = G.extension-is-a-preimage ♭ℝ-is-♭-discrete

  continuous-maps-are-images
   : (@♭ cem : Crisp-EM 𝓤₁) (h : ♭ ℝ → ♭ ℝ) → is-ε-δ-continuous h
   → fiber ♭-action h
  continuous-maps-are-images = G.continuous-maps-are-images ♭ℝ-is-♭-discrete

  Shulman-Corollary-11-6
   : (@♭ cem : Crisp-EM 𝓤₁)
   → is-embedding (♭-action {𝓤₁} {𝓤₁} {ℝ} {ℝ})
   × ((h : ♭ ℝ → ♭ ℝ) → fiber ♭-action h ↔ is-ε-δ-continuous h)
  Shulman-Corollary-11-6 =
   G.Shulman-Corollary-11-6 ♭ℝ-is-♭-discrete identity-of-ℝ-rises

  crisp-functions-are-the-continuous-maps
   : (@♭ cem : Crisp-EM 𝓤₁)
   → ♭ (ℝ → ℝ) ≃ (Σ h ꞉ (♭ ℝ → ♭ ℝ) , is-ε-δ-continuous h)
  crisp-functions-are-the-continuous-maps =
   G.crisp-functions-are-the-continuous-maps ♭ℝ-is-♭-discrete
    identity-of-ℝ-rises

\end{code}
