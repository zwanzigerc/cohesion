Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 11 November 2026. See the AI disclosure in
gist.RealCohesion.index.

The extension of an ε-δ continuous map on the crisp reals to a crisp
function ℝ → ℝ.

Let h : ♭ ℝ → ♭ ℝ be crisp and ε-δ continuous
(gist.RealCohesion.CrispUniformContinuity), and write g y for the real
number ♭-counit (h y). For every real x, crisp or not, we define a real
number G x by its Dedekind cuts:

 * p < G x if some rational interval (a , b) around x and some
   rational p' > p have p' < g at every crisp rational point of
   (a , b);

 * G x < q if some rational interval (a , b) around x and some
   rational q' < q have g < q' at every crisp rational point of
   (a , b).

The cuts quantify over crisp rationals, elements of ♭ ℚ, rather than
over crisp reals, so that they are propositions in the lowest
universe, as TypeTopology's Dedekind cuts must be. The cuts are
rounded by construction. They are disjoint because two rational
intervals around x have a common rational point, which is crisp. They
are inhabited and located because around every real x, h oscillates by
less than any given ε on the crisp points of some rational interval;
this uses the uniform continuity of h on bounded intervals, proved
from crisp excluded middle. The definition of G uses only crisp data,
so G is a crisp function when h, the proof of its continuity and crisp
excluded middle are crisp.

At a crisp point t, G t is g (t ^♭). One inequality uses continuity at
t to find a rational interval around t on which g stays above any
given rational below g (t ^♭). For the other, if g (t ^♭) were below a
lower bound p' of g near t, continuity at t would give a crisp
rational point near t where g is below p'.

This is the extension step of Shulman's proof of Corollary 11.6 [1],
which, as Fable's note describes it, extends a locally uniformly
continuous function from the rationals [2, Part A.4]. Here the values
of h are reals, so we extend directly from the crisp rational points.

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3

[2] Fable. Shulman's stated questions: three updates, Part A.
    Working note, 10 November 2026, audited by GPT-6 Astra.
    references/F18-shulman-three-updates.md

\begin{code}

{-# OPTIONS --safe --without-K --cohesion --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import gist.CohesiveApartness.Flat

module gist.RealCohesion.CrispExtension
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
       where

open import Notation.CanonicalMap
open import Notation.Order
open import UF.Base
open import UF.Powerset
open import Rationals.Type
open import Rationals.Order
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import Rationals.Positive using (ℚ₊)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import DedekindReals.Properties fe pe pt using (ℝ-arithmetically-located)
open import MetricSpaces.DedekindReals fe pe pt using (B-ℝ)
open import gist.RealCohesion.RationalArithmetic
 using (add-difference ; <-sub-right ; <-add-right)
open import gist.RealCohesion.RationalPoints fe pe pt
open import gist.RealCohesion.RealOrder fe pe pt
 using (cuts-are-ordered ; not-below-and-above)
open import gist.RealCohesion.RealLattice fe pe pt
 using (ℚ<ℝ-is-prop ; equal-if-lower-cuts-agree)
open import gist.RealCohesion.RealLimits fe pe pt using (ℚ<-add-left)
open import gist.RealCohesion.RealBalls fe pe pt
 hiding (minus-positive-is-below ; gap-from-margin ; twice-a-quarter ;
          quarter-is-positive ;
         below-by-half-margin ; quarters-leave-a-gap)
open import gist.RealCohesion.RealBalls fe pe pt
 using (below-by-half-margin ; quarters-leave-a-gap) public
open import gist.RealCohesion.CrispRationals
 using (ℚ-has-crisp-representatives ; crisp-elim)
open import gist.RealCohesion.CrispRealAnalysis fe pe pt
 using (crisp-rational-between) public
open import gist.RealCohesion.CrispUniformContinuity fe pe pt

open PropositionalTruncation pt

\end{code}

Crisp rational points. A crisp rational between two rationals is given
by crisp-rational-between of gist.RealCohesion.CrispRealAnalysis,
which is re-exported here. Two rational facts used below,
below-by-half-margin and quarters-leave-a-gap, are in
gist.RealCohesion.RealBalls, and re-exported here.

\begin{code}

♭ι : ♭ ℚ → ♭ ℝ
♭ι (r ^♭) = (ιₐ r) ^♭


\end{code}

We fix a crisp ε-δ continuous map h, and assume crisp excluded middle.

\begin{code}

module extension
        (@♭ cem : Crisp-EM 𝓤₁)
        (@♭ h : ♭ ℝ → ♭ ℝ)
        (@♭ h-is-continuous : is-ε-δ-continuous h)
       where

 open uniform-continuity cem h h-is-continuous

 Lower-Bound Upper-Bound : ℚ → ℚ → ℚ → 𝓤₀ ̇
 Lower-Bound a b p = (u : ♭ ℚ) → a < ♭-counit u → ♭-counit u < b → p < g (♭ι u)
 Upper-Bound a b q = (u : ♭ ℚ) → a < ♭-counit u → ♭-counit u < b → g (♭ι u) < q

\end{code}

Bounds near a crisp rational point, from small oscillation.

\begin{code}

 oscillation-at-rationals
  : (ε a b : ℚ) → Small-Oscillation ε a b
  → (u v : ♭ ℚ)
  → a < ♭-counit u → ♭-counit u < b → a < ♭-counit v → ♭-counit v < b
  → Close ε (g (♭ι u)) (g (♭ι v))
 oscillation-at-rationals ε a b osc (r ^♭) (s ^♭) p q p' q' =
  osc ((ιₐ r) ^♭) ((ιₐ s) ^♭)
   (ιₐ-lower a r p) (ιₐ-upper r b q) (ιₐ-lower a s p') (ιₐ-upper s b q')

 lower-bound-from-oscillation
  : (ε a b s : ℚ) (u : ♭ ℚ)
  → Small-Oscillation ε a b
  → a < ♭-counit u → ♭-counit u < b
  → s < g (♭ι u)
  → Lower-Bound a b (s ℚ- ε)
 lower-bound-from-oscillation ε a b s u osc m n k v o o' =
  Close-below ε (g (♭ι v)) (g (♭ι u))
   (oscillation-at-rationals ε a b osc v u o o' m n) s k

 upper-bound-from-oscillation
  : (ε a b s : ℚ) (u : ♭ ℚ)
  → Small-Oscillation ε a b
  → a < ♭-counit u → ♭-counit u < b
  → g (♭ι u) < s
  → Upper-Bound a b (s ℚ+ ε)
 upper-bound-from-oscillation ε a b s u osc m n k v o o' =
  Close-above ε (g (♭ι v)) (g (♭ι u))
   (oscillation-at-rationals ε a b osc v u o o' m n) s k

\end{code}

The cuts.

\begin{code}

 Below-Witness Above-Witness : ℝ → ℚ → 𝓤₀ ̇
 Below-Witness x p =
  Σ (a , b , p') ꞉ ℚ × ℚ × ℚ , (a < x) × (x < b) × (p < p') × Lower-Bound a b p'
 Above-Witness x q =
  Σ (a , b , q') ꞉ ℚ × ℚ × ℚ , (a < x) × (x < b) × (q' < q) × Upper-Bound a b q'

 Below Above : ℝ → ℚ → 𝓤₀ ̇
 Below x p = ∥ Below-Witness x p ∥
 Above x q = ∥ Above-Witness x q ∥

\end{code}

Witnesses are built by the following two functions, whose rational
arguments are variables. Building them in place, with rational
expressions such as s - 1 as components, makes Agda unfold the
rational arithmetic when it checks the remaining components, and
checking takes minutes.

\begin{code}

 below-witness : (x : ℝ) (p a b p' : ℚ)
               → a < x → x < b → p < p' → Lower-Bound a b p'
               → Below-Witness x p
 below-witness x p a b p' m n o k = (a , b , p') , m , n , o , k

 above-witness : (x : ℝ) (q a b q' : ℚ)
               → a < x → x < b → q' < q → Upper-Bound a b q'
               → Above-Witness x q
 above-witness x q a b q' m n o k = (a , b , q') , m , n , o , k

 below-by-one : (x : ℝ) (a b s : ℚ) → a < x → x < b
              → Lower-Bound a b (s ℚ- 1ℚ) → Σ p ꞉ ℚ , Below x p
 below-by-one x a b s m n k =
  (s ℚ- 1ℚ) ℚ- 1ℚ ,
  ∣ below-witness x ((s ℚ- 1ℚ) ℚ- 1ℚ) a b (s ℚ- 1ℚ) m n
     (minus-positive-is-below (s ℚ- 1ℚ) 1ℚ 0<1) k ∣

 above-by-one : (x : ℝ) (a b s : ℚ) → a < x → x < b
              → Upper-Bound a b (s ℚ+ 1ℚ) → Σ q ꞉ ℚ , Above x q
 above-by-one x a b s m n k =
  (s ℚ+ 1ℚ) ℚ+ 1ℚ ,
  ∣ above-witness x ((s ℚ+ 1ℚ) ℚ+ 1ℚ) a b (s ℚ+ 1ℚ) m n
     (ℚ<-addition-preserves-order'' (s ℚ+ 1ℚ) 1ℚ 0<1) k ∣

 below-from-margin : (x : ℝ) (p a b s ε : ℚ) → a < x → x < b
                 → (p ℚ+ ε) < s → Lower-Bound a b (s ℚ- ε) → Below-Witness x p
 below-from-margin x p a b s ε m n d k =
  below-witness x p a b (s ℚ- ε) m n (<-sub-right p s ε d) k

 above-from-margin : (x : ℝ) (q a b s ε : ℚ) → a < x → x < b
                 → s < (q ℚ- ε) → Upper-Bound a b (s ℚ+ ε) → Above-Witness x q
 above-from-margin x q a b s ε m n d k =
  above-witness x q a b (s ℚ+ ε) m n (<-add-right s q ε d) k

\end{code}

Inhabitedness.

\begin{code}

 below-from-oscillation
  : (x : ℝ) (a b : ℚ) → a < x → x < b → Small-Oscillation 1ℚ a b
  → ∃ p ꞉ ℚ , Below x p
 below-from-oscillation x a b m n osc =
  γ (crisp-rational-between a b (cuts-are-ordered x a b m n))
  where
   γ : (Σ u ꞉ ♭ ℚ , (a < ♭-counit u) × (♭-counit u < b)) → ∃ p ꞉ ℚ , Below x p
   γ (u , o , o') = ∥∥-functor δ (inhabited-from-real-L (g (♭ι u)))
    where
     δ : (Σ s ꞉ ℚ , s < g (♭ι u)) → Σ p ꞉ ℚ , Below x p
     δ (s , k) = below-by-one x a b s m n
                  (lower-bound-from-oscillation 1ℚ a b s u osc o o' k)

 above-from-oscillation
  : (x : ℝ) (a b : ℚ) → a < x → x < b → Small-Oscillation 1ℚ a b
  → ∃ q ꞉ ℚ , Above x q
 above-from-oscillation x a b m n osc =
  γ (crisp-rational-between a b (cuts-are-ordered x a b m n))
  where
   γ : (Σ u ꞉ ♭ ℚ , (a < ♭-counit u) × (♭-counit u < b)) → ∃ q ꞉ ℚ , Above x q
   γ (u , o , o') = ∥∥-functor δ (inhabited-from-real-R (g (♭ι u)))
    where
     δ : (Σ s ꞉ ℚ , g (♭ι u) < s) → Σ q ꞉ ℚ , Above x q
     δ (s , k) = above-by-one x a b s m n
                  (upper-bound-from-oscillation 1ℚ a b s u osc o o' k)

 Below-is-inhabited : (x : ℝ) → ∃ p ꞉ ℚ , Below x p
 Below-is-inhabited x = ∥∥-rec ∃-is-prop γ (small-oscillation-around x 1ℚ 0<1)
  where
   γ : (Σ (a , b) ꞉ ℚ × ℚ , (a < x) × (x < b) × Small-Oscillation 1ℚ a b)
     → ∃ p ꞉ ℚ , Below x p
   γ ((a , b) , m , n , osc) = below-from-oscillation x a b m n osc

 Above-is-inhabited : (x : ℝ) → ∃ q ꞉ ℚ , Above x q
 Above-is-inhabited x = ∥∥-rec ∃-is-prop γ (small-oscillation-around x 1ℚ 0<1)
  where
   γ : (Σ (a , b) ꞉ ℚ × ℚ , (a < x) × (x < b) × Small-Oscillation 1ℚ a b)
     → ∃ q ꞉ ℚ , Above x q
   γ ((a , b) , m , n , osc) = above-from-oscillation x a b m n osc

\end{code}

Roundedness.

\begin{code}

 Below-is-rounded : (x : ℝ) (p : ℚ)
                  → Below x p ↔ (∃ p'' ꞉ ℚ , (p < p'') × Below x p'')
 Below-is-rounded x p = α , β
  where
   α : Below x p → ∃ p'' ꞉ ℚ , (p < p'') × Below x p''
   α = ∥∥-functor γ
    where
     γ : Below-Witness x p → Σ p'' ꞉ ℚ , (p < p'') × Below x p''
     γ ((a , b , p') , m , n , o , k) = δ (ℚ-dense p p' o)
      where
       δ : (Σ p'' ꞉ ℚ , (p < p'') × (p'' < p'))
         → Σ p'' ꞉ ℚ , (p < p'') × Below x p''
       δ (p'' , c , d) = p'' , c , ∣ below-witness x p'' a b p' m n d k ∣

   β : (∃ p'' ꞉ ℚ , (p < p'') × Below x p'') → Below x p
   β = ∥∥-rec ∃-is-prop γ
    where
     γ : (Σ p'' ꞉ ℚ , (p < p'') × Below x p'') → Below x p
     γ (p'' , o , l) = ∥∥-functor δ l
      where
       δ : Below-Witness x p'' → Below-Witness x p
       δ ((a , b , p') , m , n , o' , k) =
        below-witness x p a b p' m n (ℚ<-trans p p'' p' o o') k

 Above-is-rounded : (x : ℝ) (q : ℚ)
                  → Above x q ↔ (∃ q'' ꞉ ℚ , (q'' < q) × Above x q'')
 Above-is-rounded x q = α , β
  where
   α : Above x q → ∃ q'' ꞉ ℚ , (q'' < q) × Above x q''
   α = ∥∥-functor γ
    where
     γ : Above-Witness x q → Σ q'' ꞉ ℚ , (q'' < q) × Above x q''
     γ ((a , b , q') , m , n , o , k) = δ (ℚ-dense q' q o)
      where
       δ : (Σ q'' ꞉ ℚ , (q' < q'') × (q'' < q))
         → Σ q'' ꞉ ℚ , (q'' < q) × Above x q''
       δ (q'' , c , d) = q'' , d , ∣ above-witness x q'' a b q' m n c k ∣

   β : (∃ q'' ꞉ ℚ , (q'' < q) × Above x q'') → Above x q
   β = ∥∥-rec ∃-is-prop γ
    where
     γ : (Σ q'' ꞉ ℚ , (q'' < q) × Above x q'') → Above x q
     γ (q'' , o , l) = ∥∥-functor δ l
      where
       δ : Above-Witness x q'' → Above-Witness x q
       δ ((a , b , q') , m , n , o' , k) =
        above-witness x q a b q' m n (ℚ<-trans q' q'' q o' o) k

\end{code}

Disjointness: a common crisp rational point separates the bounds.

\begin{code}

 bounds-are-ordered
  : (p q a b p' a' b' q' : ℚ)
  → p < p' → q' < q
  → Lower-Bound a b p' → Upper-Bound a' b' q'
  → (Σ r ꞉ ℚ , ((a < r) × (r < b)) × ((a' < r) × (r < b')))
  → p < q
 bounds-are-ordered p q a b p' a' b' q' o o' k k' (r , (c , d) , (c' , d')) =
  crisp-elim ℚ-has-crisp-representatives
   (λ r → a < r → r < b → a' < r → r < b' → p < q)
   (λ r₀ c d c' d' → ℚ<-trans p p' q o
                      (ℚ<-trans p' q' q
                        (cuts-are-ordered (g (♭ι (r₀ ^♭))) p' q'
                          (k (r₀ ^♭) c d) (k' (r₀ ^♭) c' d'))
                        o'))
   r c d c' d'

 Below-Above-disjoint : (x : ℝ) (p q : ℚ) → Below x p × Above x q → p < q
 Below-Above-disjoint x p q (l , r) =
  ∥∥-rec (ℚ<-is-prop p q) γ (binary-choice l r)
  where
   γ : Below-Witness x p × Above-Witness x q → p < q
   γ (((a , b , p') , m , n , o , k) , ((a' , b' , q') , m' , n' , o' , k')) =
    ∥∥-rec (ℚ<-is-prop p q) (bounds-are-ordered p q a b p' a' b' q' o o' k k')
     (common-rational-point x a b a' b' m n m' n')

\end{code}

Locatedness.

\begin{code}

 located-from-oscillation
  : (x : ℝ) (p q ε a b : ℚ)
  → (p ℚ+ ε) < (q ℚ- ε)
  → a < x → x < b
  → Small-Oscillation ε a b
  → Below x p ∨ Above x q
 located-from-oscillation x p q ε a b gap m n osc =
  γ (crisp-rational-between a b (cuts-are-ordered x a b m n))
  where
   γ : (Σ u ꞉ ♭ ℚ , (a < ♭-counit u) × (♭-counit u < b)) → Below x p ∨ Above x q
   γ (u , o , o') =
    ∥∥-functor δ (ℝ-locatedness (g (♭ι u)) (p ℚ+ ε) (q ℚ- ε) gap)
    where
     δ : ((p ℚ+ ε) < g (♭ι u)) ∔ (g (♭ι u) < (q ℚ- ε)) → Below x p ∔ Above x q
     δ (inl c) = inl (∥∥-functor ζ (rounded-left-d (g (♭ι u)) (p ℚ+ ε) c))
      where
       ζ : (Σ s ꞉ ℚ , (p ℚ+ ε) < s < g (♭ι u)) → Below-Witness x p
       ζ (s , d , d') = below-from-margin x p a b s ε m n d
                         (lower-bound-from-oscillation ε a b s u osc o o' d')
     δ (inr c) = inr (∥∥-functor ζ (rounded-right-b (upper-cut-of (g (♭ι u)))
                                     (rounded-from-real-R (g (♭ι u))) (q ℚ- ε)
                                      c))
      where
       ζ : (Σ s ꞉ ℚ , (s < q ℚ- ε) × (g (♭ι u) < s)) → Above-Witness x q
       ζ (s , d , d') = above-from-margin x q a b s ε m n d
                         (upper-bound-from-oscillation ε a b s u osc o o' d')

 located-gap : (p q : ℚ) → p < q
             → (p ℚ+ halfₐ (halfₐ (q ℚ- p))) < (q ℚ- halfₐ (halfₐ (q ℚ- p)))
 located-gap = quarters-leave-a-gap

 Below-Above-located : (x : ℝ) (p q : ℚ) → p < q → Below x p ∨ Above x q
 Below-Above-located x p q l =
  ∥∥-rec ∨-is-prop γ
   (small-oscillation-around x (halfₐ (halfₐ (q ℚ- p)))
     (quarter-is-positive (q ℚ- p) (ℚ<-difference-positive p q l)))
  where
   γ : (Σ (a , b) ꞉ ℚ × ℚ ,
         (a < x) × (x < b) × Small-Oscillation (halfₐ (halfₐ (q ℚ- p))) a b)
     → Below x p ∨ Above x q
   γ ((a , b) , m , n , osc) =
    located-from-oscillation x p q (halfₐ (halfₐ (q ℚ- p))) a b
     (located-gap p q l) m n osc

\end{code}

The extension.

\begin{code}

 extension : ℝ → ℝ
 extension x = ((λ p → Below x p , ∃-is-prop) , (λ q → Above x q , ∃-is-prop)) ,
               Below-is-inhabited x , Above-is-inhabited x ,
               Below-is-rounded x , Above-is-rounded x ,
               Below-Above-disjoint x , Below-Above-located x

\end{code}

At crisp points the extension agrees with h.

\begin{code}

 contradiction-at-rational
  : (t v : ℝ) (a b p' s δ : ℚ)
  → Lower-Bound a b p'
  → v < s
  → ((y : ♭ ℝ) → Close δ (♭-counit y) t → Close (p' ℚ- s) (g y) v)
  → (Σ r ꞉ ℚ , (a < r) × (r < b) × Close δ (ιₐ r) t)
  → 𝟘 {𝓤₀}
 contradiction-at-rational t v a b p' s δ k c f (r , o , o' , cl) =
  crisp-elim ℚ-has-crisp-representatives
   (λ r → a < r → r < b → Close δ (ιₐ r) t → 𝟘)
   (λ r₀ o o' cl → not-below-and-above (g ((ιₐ r₀) ^♭)) p' (k (r₀ ^♭) o o')
                    (transport (g ((ιₐ r₀) ^♭) <_) (add-difference s p')
                      (Close-above (p' ℚ- s) (g ((ιₐ r₀) ^♭)) v
                        (f ((ιₐ r₀) ^♭) cl) s c)))
   r o o' cl

 lower-bound-at-crisp-point
  : (@♭ t : ℝ) (a b p' s : ℚ)
  → a < t → t < b
  → Lower-Bound a b p'
  → g (t ^♭) < s → s < p'
  → 𝟘 {𝓤₀}
 lower-bound-at-crisp-point t a b p' s m n k c d =
  ∥∥-rec 𝟘-is-prop γ
   (h-is-continuous (t ^♭) (p' ℚ- s , ℚ<-difference-positive s p' d))
  where
   γ : (Σ δ ꞉ ℚ₊ , ((y : ♭ ℝ) → B-ℝ (♭-counit y) t δ
                              → B-ℝ (g y) (g (t ^♭))
                                 (p' ℚ- s , ℚ<-difference-positive s p' d)))
     → 𝟘
   γ ((δ , l) , f) =
    ∥∥-rec 𝟘-is-prop (contradiction-at-rational t (g (t ^♭)) a b p' s δ k c f)
                      (rational-near t a b δ m n l)

 below-extension-is-below : (@♭ t : ℝ) (p : ℚ) → Below t p → p < g (t ^♭)
 below-extension-is-below t p = ∥∥-rec (ℚ<ℝ-is-prop p (g (t ^♭))) γ
  where
   γ : Below-Witness t p → p < g (t ^♭)
   γ ((a , b , p') , m , n , o , k) =
    ∥∥-rec (ℚ<ℝ-is-prop p (g (t ^♭))) δ (ℝ-locatedness (g (t ^♭)) p p' o)
    where
     δ : (p < g (t ^♭)) ∔ (g (t ^♭) < p') → p < g (t ^♭)
     δ (inl c) = c
     δ (inr c) = 𝟘-elim (∥∥-rec 𝟘-is-prop ζ
                          (rounded-right-b (upper-cut-of (g (t ^♭)))
                            (rounded-from-real-R (g (t ^♭))) p' c))
      where
       ζ : (Σ s ꞉ ℚ , (s < p') × (g (t ^♭) < s)) → 𝟘
       ζ (s , d , c') = lower-bound-at-crisp-point t a b p' s m n k c' d

 lower-bound-from-continuity
  : (t v : ℝ) (p₂ η δ a b : ℚ)
  → p₂ < v
  → ((y : ♭ ℝ) → Close δ (♭-counit y) t → Close η (g y) v)
  → a < t → t < b → b ℚ- a < δ
  → Lower-Bound a b (p₂ ℚ- η)
 lower-bound-from-continuity t v p₂ η δ a b o f c d w (r₀ ^♭) e e' =
  Close-below η (g ((ιₐ r₀) ^♭)) v
   (f ((ιₐ r₀) ^♭)
     (Close-from-interval δ a b (ιₐ r₀) t (ιₐ-lower a r₀ e) (ιₐ-upper r₀ b e') c
       d w))
   p₂ o

 lower-bound-near
  : (t v : ℝ) (p p₂ δ : ℚ)
  → p < p₂ → p₂ < v
  → ((y : ♭ ℝ) → Close δ (♭-counit y) t → Close (halfₐ (p₂ ℚ- p)) (g y) v)
  → (Σ (a , b) ꞉ ℚ × ℚ , (a < t < b) × (b ℚ- a < δ))
  → Below-Witness t p
 lower-bound-near t v p p₂ δ o o' f ((a , b) , (c , d) , w) =
  below-witness t p a b (p₂ ℚ- halfₐ (p₂ ℚ- p)) c d
   (below-by-half-margin p p₂ o)
   (lower-bound-from-continuity t v p₂ (halfₐ (p₂ ℚ- p)) δ a b o' f c d w)

 below-is-below-extension : (@♭ t : ℝ) (p : ℚ) → p < g (t ^♭) → Below t p
 below-is-below-extension t p l =
  ∥∥-rec ∃-is-prop γ (rounded-left-d (g (t ^♭)) p l)
  where
   γ : (Σ p₂ ꞉ ℚ , p < p₂ < g (t ^♭)) → Below t p
   γ (p₂ , o , o') =
    ∥∥-rec ∃-is-prop δ
     (h-is-continuous (t ^♭)
       (halfₐ (p₂ ℚ- p) ,
         halfₐ-is-positive (p₂ ℚ- p) (ℚ<-difference-positive p p₂ o)))
    where
     δ : (Σ δ ꞉ ℚ₊ , ((y : ♭ ℝ) → B-ℝ (♭-counit y) t δ
                                → B-ℝ (g y) (g (t ^♭))
                                    (halfₐ (p₂ ℚ- p) ,
                                     halfₐ-is-positive (p₂ ℚ- p)
                                      (ℚ<-difference-positive p p₂ o))))
       → Below t p
     δ ((δ' , l') , f) =
      ∥∥-functor (lower-bound-near t (g (t ^♭)) p p₂ δ' o o' f)
                          (ℝ-arithmetically-located t (δ' , l'))

 extension-agrees : (@♭ t : ℝ) → extension t ＝ g (t ^♭)
 extension-agrees t = equal-if-lower-cuts-agree (extension t) (g (t ^♭))
                       (below-extension-is-below t) (below-is-below-extension t)

\end{code}
