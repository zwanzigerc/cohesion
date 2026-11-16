Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026; made an instance of
gist.RealCohesion.RationalBoxExtension the same day. See the AI
disclosure in gist.RealCohesion.index.

The extension of an ε-δ continuous map on the crisp points of ℝⁿ to a
crisp function ℝⁿ → ℝ: the second step of the third part of Theorem 3.3
of the write-up [1] in n variables, gate G21 of Claude Fable 5.2's
second addendum [2].

Let h : ♭ ℝⁿ → ♭ ℝ be crisp and continuous in the sense of
gist.RealCohesion.ShulmanWeakeningsStatements (is-♭-continuous), and
write g u for its value at a crisp rational point u
(gist.RealCohesion.CrispUniformContinuityOnBoxes). For every real point
x, crisp or not, define a real number G x by its Dedekind cuts:

 * p < G x if some open rational box (a , b) around x and some rational
   p' > p have p' < g at every crisp rational point of (a , b);

 * G x < q if some open rational box (a , b) around x and some rational
   q' < q have g < q' at every crisp rational point of (a , b).

This is gist.RealCohesion.CrispExtension, for one variable, with
rational boxes in place of rational intervals, as the addendum [2, §3,
G21] proposes. Since gate G14 the construction is that of
gist.RealCohesion.RationalBoxExtension, for the crisp rational points as
sample points: a box around a real point contains one, two boxes around
a real point have a common one, and the values vary little on small
boxes (gist.RealCohesion.CrispUniformContinuityOnBoxes). The definition
of G uses only crisp data, so G is a crisp function when h, the proof
of its continuity and crisp excluded middle are crisp. At a crisp point
t, G t is h t, because continuity of h at t makes the values at crisp
rational points near t tend to h t. The names of this module keep their
types; some lemmas of the first version are no longer used by the
others and are kept for that reason.

[1] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, revision of 12 November 2026, Theorem 3.3.
    references/C04-write-up-2026-11-12.tex

[2] Claude Fable 5.2. Second addendum to the formalization plan,
    revision 4 of 12 November 2026.
    references/F13b-second-addendum-rev4-as-amended.md

\begin{code}

{-# OPTIONS --safe --without-K --cohesion --lossy-unification #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import gist.CohesiveApartness.Flat

module gist.RealCohesion.CrispExtensionOnBoxes
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
       where

open import Fin.Type
open import Notation.CanonicalMap
open import Notation.Order
open import UF.Base
open import UF.Powerset
open import Rationals.Type
open import Rationals.Order
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Negation renaming (_-_ to _ℚ-_ ; -_ to ℚ-_)
open import DedekindReals.Type fe pe pt
open import DedekindReals.Order fe pe pt
open import DedekindReals.Properties fe pe pt using (ℝ-arithmetically-located)
open import gist.RealCohesion.BrouwerStatements fe pe pt using (ℝ^)
open import gist.RealCohesion.ShulmanWeakeningsStatements fe pe pt
 using
  (is-♭-continuous ; _is-strictly-within_of_ ; _is-coordinatewise-within_of_)
open import gist.RealCohesion.ContinuityForms fe pe pt
 using (within-from-close ; close-from-within ; interval-gives-strictly-close ;
        strictly-close-below ; strictly-close-above)
open import gist.RealCohesion.CrispRationals
 using (ℚ-has-crisp-representatives ; Fin-functions-have-crisp-representatives ;
        crisp-elim ; crisp-witness)
open import gist.RealCohesion.RationalArithmetic
 using (add-difference ; <-sub-right ; <-add-right)
open import gist.RealCohesion.RationalPoints fe pe pt
 using (ιₐ ; ιₐ-lower ; ιₐ-upper)
open import gist.RealCohesion.RealOrder fe pe pt
 using (cuts-are-ordered ; not-below-and-above)
open import gist.RealCohesion.RealLattice fe pe pt
 using (ℚ<ℝ-is-prop ; equal-if-lower-cuts-agree)
open import gist.RealCohesion.RealBalls fe pe pt
open import gist.RealCohesion.CrispUniformContinuityOnBoxes fe pe pt
open import gist.RealCohesion.RationalBoxExtension fe pe pt
 using (common-point ; Small-Box ; small-box-around ; within-in-a-small-box)
  public
open import gist.RealCohesion.RationalBoxExtension fe pe pt
 using (module extension-from-samples)

open PropositionalTruncation pt

\end{code}

Crisp rational points of boxes. A box around a real point contains a
crisp rational point, and two boxes around a real point contain a
common one. The other facts about boxes, common-point, Small-Box,
small-box-around and within-in-a-small-box, are in
gist.RealCohesion.RationalBoxExtension and re-exported here.

\begin{code}

crisp-point-in-box : {@♭ n : ℕ} (a b : Fin n → ℚ) (x : ℝ^ n) → Around a b x
                   → Σ u ꞉ ♭ (Fin n → ℚ) , In-Box a b (♭-counit u)
crisp-point-in-box {n} a b x m =
 crisp-witness
  (Fin-functions-have-crisp-representatives fe n 0ℚ ℚ-has-crisp-representatives)
  (In-Box a b) (λ i → pr₁ (between i)) (λ i → pr₂ (between i))
 where
  between : (i : Fin n) → Σ c ꞉ ℚ , (a i < c) × (c < b i)
  between i = ℚ-dense (a i) (b i)
               (cuts-are-ordered (x i) (a i) (b i) (pr₁ (m i)) (pr₂ (m i)))

crisp-common-point : {@♭ n : ℕ} (x : ℝ^ n) (a b a' b' : Fin n → ℚ)
                   → Around a b x → Around a' b' x
                   → ∃ u ꞉ ♭ (Fin n → ℚ) ,
                       In-Box a b (♭-counit u) × In-Box a' b' (♭-counit u)
crisp-common-point {n} x a b a' b' m m' =
 ∥∥-functor γ (common-point x a b a' b' m m')
 where
  γ : (Σ r ꞉ (Fin n → ℚ) , In-Box a b r × In-Box a' b' r)
    → Σ u ꞉ ♭ (Fin n → ℚ) , In-Box a b (♭-counit u) × In-Box a' b' (♭-counit u)
  γ (r , k) = crisp-witness (Fin-functions-have-crisp-representatives fe n 0ℚ
                              ℚ-has-crisp-representatives)
               (λ r → In-Box a b r × In-Box a' b' r) r k

\end{code}

We fix crisp excluded middle and a crisp map h that is continuous at
crisp points. The extension is that of
gist.RealCohesion.RationalBoxExtension for the crisp rational points.

\begin{code}

module extension-on-boxes
        (@♭ cem : Crisp-EM 𝓤₀)
        {@♭ n : ℕ}
        (@♭ h : ♭ (ℝ^ n) → ♭ ℝ)
        (@♭ h-is-continuous : is-♭-continuous h)
       where

 open uniform-continuity-on-boxes cem h h-is-continuous
  using (g ; small-oscillation-around)

 open extension-from-samples (♭ (Fin n → ℚ)) ♭-counit g crisp-point-in-box
  crisp-common-point
  public
 open with-small-oscillation small-oscillation-around public

\end{code}

At crisp points the extension agrees with h: by continuity of h at a
crisp point t, the values at crisp rational points near t tend to h t.

\begin{code}

 crisp-convergence : (@♭ t : ℝ^ n) → Converges-To t (♭-counit (h (t ^♭)))
 crisp-convergence t η l = ∥∥-functor γ (h-is-continuous (t ^♭) η l)
  where
   γ : (Σ δ ꞉ ℚ , (0ℚ < δ)
                × ((y : ♭ (ℝ^ n)) → ♭-counit y is-coordinatewise-within δ of t
                                  → ♭-counit (h y) is-strictly-within η
                                     of ♭-counit (h (t ^♭))))
     → Σ δ ꞉ ℚ , (0ℚ < δ)
               × ((u : ♭ (Fin n → ℚ)) →
                 ((i : Fin n) → (ιₐ (♭-counit u i)) is-strictly-within δ of t i)
                                      → g u is-strictly-within η of ♭-counit
                                         (h (t ^♭)))
   γ (δ , l' , f) = δ , l' , φ
    where
     φ : (u : ♭ (Fin n → ℚ))
       → ((i : Fin n) → (ιₐ (♭-counit u i)) is-strictly-within δ of t i)
       → g u is-strictly-within η of ♭-counit (h (t ^♭))
     φ (u ^♭) w = f ((λ i → ιₐ (u i)) ^♭) w

 below-extension-is-below : (@♭ t : ℝ^ n) (p : ℚ) → Below t p
                          → p < ♭-counit (h (t ^♭))
 below-extension-is-below t =
  lower-cut-below-the-limit t (♭-counit (h (t ^♭))) (crisp-convergence t)

 below-is-below-extension : (@♭ t : ℝ^ n) (p : ℚ) → p < ♭-counit (h (t ^♭))
                          → Below t p
 below-is-below-extension t =
  lower-cut-from-the-limit t (♭-counit (h (t ^♭))) (crisp-convergence t)

 extension-agrees : (@♭ t : ℝ^ n) → extension t ＝ ♭-counit (h (t ^♭))
 extension-agrees t =
  extension-agrees-at t (♭-counit (h (t ^♭))) (crisp-convergence t)

\end{code}

Lemmas of the first version of this module, kept with their types; the
proofs above no longer use them.

\begin{code}

 bounds-are-ordered
  : (p q : ℚ) (a b : Fin n → ℚ) (p' : ℚ) (a' b' : Fin n → ℚ) (q' : ℚ)
  → p < p' → q' < q
  → Lower-Bound a b p' → Upper-Bound a' b' q'
  → (Σ r ꞉ (Fin n → ℚ) , In-Box a b r × In-Box a' b' r)
  → p < q
 bounds-are-ordered p q a b p' a' b' q' o o' k k' (r , c , c') =
  crisp-elim (Fin-functions-have-crisp-representatives fe n 0ℚ
               ℚ-has-crisp-representatives)
   (λ r → In-Box a b r → In-Box a' b' r → p < q)
   (λ r₀ c c' → ℚ<-trans p p' q o
                 (ℚ<-trans p' q' q
                   (cuts-are-ordered (g (r₀ ^♭)) p' q' (k (r₀ ^♭) c)
                     (k' (r₀ ^♭) c'))
                   o'))
   r c c'

 rational-point-near
  : (t : ℝ^ n) (a b : Fin n → ℚ) (δ : ℚ) → Around a b t → 0ℚ < δ
  → ∃ r ꞉ (Fin n → ℚ) ,
      In-Box a b r × ((λ i → ιₐ (r i)) is-coordinatewise-within δ of t)
 rational-point-near t a b δ m l = ∥∥-rec ∃-is-prop γ (small-box-around t δ l)
  where
   γ : Small-Box t δ
     → ∃ r ꞉ (Fin n → ℚ) ,
         In-Box a b r × ((λ i → ιₐ (r i)) is-coordinatewise-within δ of t)
   γ ((c , e) , m' , w) = ∥∥-functor δ' (common-point t a b c e m m')
    where
     δ' : (Σ r ꞉ (Fin n → ℚ) , In-Box a b r × In-Box c e r)
        → Σ r ꞉ (Fin n → ℚ) , In-Box a b r
                            × ((λ i → ιₐ (r i)) is-coordinatewise-within δ of t)
     δ' (r , k , k') = r , k , within-in-a-small-box δ c e r t m' k' w

 contradiction-at-rational-point
  : (t : ℝ^ n) (v : ℝ) (a b : Fin n → ℚ) (p' s δ : ℚ)
  → Lower-Bound a b p'
  → v < s
  → ((y : ♭ (ℝ^ n)) → ♭-counit y is-coordinatewise-within δ of t
                    → ♭-counit (h y) is-strictly-within (p' ℚ- s) of v)
  → (Σ r ꞉ (Fin n → ℚ) ,
      In-Box a b r × ((λ i → ιₐ (r i)) is-coordinatewise-within δ of t))
  → 𝟘 {𝓤₀}
 contradiction-at-rational-point t v a b p' s δ k c f (r , o , cl) =
  crisp-elim (Fin-functions-have-crisp-representatives fe n 0ℚ
               ℚ-has-crisp-representatives)
   (λ r → In-Box a b r → ((λ i → ιₐ (r i)) is-coordinatewise-within δ of t) → 𝟘)
   (λ r₀ o cl → not-below-and-above (g (r₀ ^♭)) p' (k (r₀ ^♭) o)
                 (transport (g (r₀ ^♭) <_) (add-difference s p')
                   (strictly-close-above (p' ℚ- s) (g (r₀ ^♭)) v
                     (pr₁ (close-from-within (p' ℚ- s) (g (r₀ ^♭)) v
                            (f ((λ i → ιₐ (r₀ i)) ^♭) cl)))
                     s c)))
   r o cl

 lower-bound-at-crisp-point
  : (@♭ t : ℝ^ n) (a b : Fin n → ℚ) (p' s : ℚ)
  → Around a b t
  → Lower-Bound a b p'
  → ♭-counit (h (t ^♭)) < s → s < p'
  → 𝟘 {𝓤₀}
 lower-bound-at-crisp-point t a b p' s m k c d =
  ∥∥-rec 𝟘-is-prop γ
   (h-is-continuous (t ^♭) (p' ℚ- s) (ℚ<-difference-positive s p' d))
  where
   γ : (Σ δ ꞉ ℚ , (0ℚ < δ)
                × ((y : ♭ (ℝ^ n)) → ♭-counit y is-coordinatewise-within δ of t
                                  → ♭-counit (h y) is-strictly-within (p' ℚ- s)
                                                   of ♭-counit (h (t ^♭))))
     → 𝟘
   γ (δ , l , f) =
    ∥∥-rec 𝟘-is-prop
     (contradiction-at-rational-point t (♭-counit (h (t ^♭))) a b p' s δ k c f)
     (rational-point-near t a b δ m l)

 lower-bound-from-continuity
  : (t : ℝ^ n) (v : ℝ) (p₂ η δ : ℚ) (a b : Fin n → ℚ)
  → p₂ < v
  → ((y : ♭ (ℝ^ n)) → ♭-counit y is-coordinatewise-within δ of t
                    → ♭-counit (h y) is-strictly-within η of v)
  → Around a b t → ((i : Fin n) → b i ℚ- a i < δ)
  → Lower-Bound a b (p₂ ℚ- η)
 lower-bound-from-continuity t v p₂ η δ a b o f m w (r ^♭) e =
  strictly-close-below η (g (r ^♭)) v
   (pr₂ (close-from-within η (g (r ^♭)) v
          (f ((λ i → ιₐ (r i)) ^♭) (within-in-a-small-box δ a b r t m e w))))
   p₂ o

 lower-bound-near
  : (t : ℝ^ n) (v : ℝ) (p p₂ δ : ℚ)
  → p < p₂ → p₂ < v
  → ((y : ♭ (ℝ^ n)) → ♭-counit y is-coordinatewise-within δ of t
                    → ♭-counit (h y) is-strictly-within halfₐ (p₂ ℚ- p) of v)
  → Small-Box t δ
  → Below-Witness t p
 lower-bound-near t v p p₂ δ o o' f ((a , b) , m , w) =
  below-witness t p a b (p₂ ℚ- halfₐ (p₂ ℚ- p)) m (below-by-half-margin p p₂ o)
   (lower-bound-from-continuity t v p₂ (halfₐ (p₂ ℚ- p)) δ a b o' f m w)

\end{code}
