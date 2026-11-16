Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 11 November 2026. See the AI disclosure in
gist.RealCohesion.index.

The grid and the labels of the proof of Corollary 3.7 of the write-up
[1], in the cube form of Claude Fable 5.2's blueprint addendum [2]:
gate G10, §5.2 of the addendum.

The write-up takes a crisp map F from ℝⁿ to the cube C = [-1,1]ⁿ. For
m ≥ 0 it lets G_m be the grid of the points u of C with
u_i = -1 + 2^(1-m) k_i, where 0 ≤ k_i ≤ 2^m, and puts l_i(u) = 1 if
u_i = 1, or if u_i > -1 and F_i(u) < u_i, and l_i(u) = 0 otherwise.
Grid points are rational, so they may be assumed crisp, and then the
comparison F_i(u) < u_i is decided by crisp excluded middle. By
construction l_i(u) = 0 if u_i = -1, and l_i(u) = 1 if u_i = 1.
Moreover l_i(u) = 0 gives u_i ≤ F_i(u), and l_i(u) = 1 gives
F_i(u) ≤ u_i; on the two faces this holds because F takes values in C.

The formal statements are these, in the following form.

 * Grid points are indexed by vectors a : Fin n → ℕ, the k of the
   write-up: grid-point m a is the rational point with coordinates
   -1 + 2^(1-m) · a i. The side 2^m is succ (side m), without
   subtraction. These rational definitions are in
   gist.RealCohesion.RationalGrid and re-exported here. In range, that
   is, if a i ≤ 2^m for all i, the grid point lies in the cube
   (grid-points-are-in-cube).

 * label m a i is l_i at the grid point, defined from a: ₁ if
   a i ＝ 2^m, otherwise ₀ if a i ＝ 0, otherwise the decision of
   F (grid-point m a) i < grid-point m a i. In range, a i ＝ 0 and
   a i ＝ 2^m say that the grid point lies on the two faces
   (grid-point-on-lower-face and grid-point-on-upper-face).

 * The two facts "by construction" are labels-on-lower-faces and
   labels-on-upper-faces, stated exactly as the two hypotheses of
   Kuhn-Lemma n (gist.RealCohesion.KuhnLemma), so that Kuhn's lemma
   applies to side m and label m. The addendum calls them L1.

 * The two inequalities are label-₀-gives-below and
   label-₁-gives-above, for every a, in range or not. The addendum
   calls them L2.

 * Crisp excluded middle decides crisp propositions, so the
   comparison has to be made crisp in m, a and i. The level and the
   vector have crisp representatives (gist.RealCohesion.CrispRationals).
   We don't know that the coordinate i : Fin n has one, for crisp n,
   without crisp induction on n. So we decide instead, for k : ℕ, that
   the coordinate with number k, if there is one, moves down, and use
   that at k = ⟦ i ⟧, the number of i (TypeTopology's embedding
   Fin n → ℕ).

The map F and crisp excluded middle for propositions in 𝓤₀ must be
crisp. That F takes values in the cube is an ordinary hypothesis,
used only for the two inequalities.

[1] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, seventh revision of 11 November 2026,
    proof of Corollary 3.7, paragraph "Labels".
    references/C03-write-up-2026-11-11-seventh.tex
    references/C03a-write-up-seventh-README.txt

[2] Claude Fable 5.2. Formalization blueprint, addendum, revision 4 of
    11 November 2026, §5.2.
    references/F14-brouwer-addendum-rev4.md

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import gist.CohesiveApartness.Flat

module gist.RealCohesion.CubeGrid
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
       where

open import Fin.Embeddings using (⟦_⟧ ; ⟦_⟧-lc)
open import Fin.Type
open import MLTT.Two-Properties using (zero-is-not-one ; one-is-not-zero)
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Naturals.Order
open import Naturals.Properties using (positive-not-zero)
open import Notation.CanonicalMap
open import Notation.Order
open import Rationals.Addition
open import Rationals.Order
open import Rationals.Type
open import UF.DiscreteAndSeparated using (ℕ-is-discrete ; ℕ-is-set)
open import DedekindReals.Order fe pe pt
open import DedekindReals.Type fe pe pt
open import gist.RealCohesion.BrouwerStatements fe pe pt
 using (ℝ^ ; in-cube ; rational-point)
open import gist.RealCohesion.CrispRationals
 using (ℕ-has-crisp-representatives ; ×-has-crisp-representatives ;
        Fin-functions-have-crisp-representatives ; decide-at)
open import gist.RealCohesion.RealOrder fe pe pt
 using (ℝ<-gives-≤ ; embedding-preserves-≤)

\end{code}

The rational grid is in gist.RealCohesion.RationalGrid, a module without
parameters, and is re-exported here. In range, grid points lie in the
cube.

\begin{code}

open import gist.RealCohesion.RationalGrid public

grid-points-are-in-cube : {n : ℕ} (m : ℕ) (a : Fin n → ℕ)
                        → ((i : Fin n) → a i ≤ succ (side m))
                        → in-cube (rational-point (grid-point m a))
grid-points-are-in-cube m a l i =
 embedding-preserves-≤ -1ℚ (grid-point m a i) (pr₁ (grid-point-bounds m a l i))
  ,
 embedding-preserves-≤ (grid-point m a i) 1ℚ (pr₂ (grid-point-bounds m a l i))

\end{code}

The bit of three decisions: ₁ if the first holds, otherwise ₀ if the
second holds, otherwise ₁ or ₀ according as the third holds or not.

\begin{code}

label-bit : {𝓤 𝓥 𝓦 : Universe} {A : 𝓤 ̇ } {B : 𝓥 ̇ } {C : 𝓦 ̇ }
          → is-decidable A → is-decidable B → is-decidable C → 𝟚
label-bit (inl _) _       _       = ₁
label-bit (inr _) (inl _) _       = ₀
label-bit (inr _) (inr _) (inl _) = ₁
label-bit (inr _) (inr _) (inr _) = ₀

module _ {𝓤 𝓥 𝓦 : Universe} {A : 𝓤 ̇ } {B : 𝓥 ̇ } {C : 𝓦 ̇ } where

 label-bit-of-first
  : (dA : is-decidable A) (dB : is-decidable B) (dC : is-decidable C)
                    → A → label-bit dA dB dC ＝ ₁
 label-bit-of-first (inl _) dB dC a = refl
 label-bit-of-first (inr ν) dB dC a = 𝟘-elim (ν a)

 label-bit-of-second
  : (dA : is-decidable A) (dB : is-decidable B) (dC : is-decidable C)
                     → ¬ A → B → label-bit dA dB dC ＝ ₀
 label-bit-of-second (inl a) dB       dC ν b = 𝟘-elim (ν a)
 label-bit-of-second (inr _) (inl _)  dC ν b = refl
 label-bit-of-second (inr _) (inr ν') dC ν b = 𝟘-elim (ν' b)

 label-bit-₀ : (dA : is-decidable A) (dB : is-decidable B) (dC : is-decidable C)
             → label-bit dA dB dC ＝ ₀ → B ∔ ¬ C
 label-bit-₀ (inl _) dB      dC      e = 𝟘-elim (one-is-not-zero e)
 label-bit-₀ (inr _) (inl b) dC      e = inl b
 label-bit-₀ (inr _) (inr _) (inl _) e = 𝟘-elim (one-is-not-zero e)
 label-bit-₀ (inr _) (inr _) (inr ν) e = inr ν

 label-bit-₁ : (dA : is-decidable A) (dB : is-decidable B) (dC : is-decidable C)
             → label-bit dA dB dC ＝ ₁ → A ∔ C
 label-bit-₁ (inl a) dB      dC      e = inl a
 label-bit-₁ (inr _) (inl _) dC      e = 𝟘-elim (zero-is-not-one e)
 label-bit-₁ (inr _) (inr _) (inl c) e = inr c
 label-bit-₁ (inr _) (inr _) (inr _) e = 𝟘-elim (zero-is-not-one e)

\end{code}

The labels, for crisp excluded middle and a crisp map F. The
proposition decided is Moves-Down (m , a , k): the coordinate with
number k of F at the grid point is below that of the grid point.

\begin{code}

module _ (@♭ cem : Crisp-EM 𝓤₀)
         {@♭ n : ℕ}
         (@♭ F : ℝ^ n → ℝ^ n)
       where

 Moves-Down : ℕ × (Fin n → ℕ) × ℕ → 𝓤₀ ̇
 Moves-Down (m , a , k) =
  Σ i ꞉ Fin n , (⟦ i ⟧ ＝ k)
              × (F (rational-point (grid-point m a)) i < ι (grid-point m a i))

 Moves-Down-is-prop : (x : ℕ × (Fin n → ℕ) × ℕ) → is-prop (Moves-Down x)
 Moves-Down-is-prop (m , a , k) (i , e , o) (i' , e' , o') =
  to-subtype-＝
   (λ j → ×-is-prop ℕ-is-set
           (<-is-prop (F (rational-point (grid-point m a)) j)
             (ι (grid-point m a j))))
   (⟦_⟧-lc n (e ∙ e' ⁻¹))

 moves-down-decision : (m : ℕ) (a : Fin n → ℕ) (i : Fin n)
                     → is-decidable (Moves-Down (m , a , ⟦ i ⟧))
 moves-down-decision m a i =
  decide-at (×-has-crisp-representatives ℕ-has-crisp-representatives
              (×-has-crisp-representatives
                (Fin-functions-have-crisp-representatives fe n 0
                  ℕ-has-crisp-representatives)
                ℕ-has-crisp-representatives))
   cem Moves-Down Moves-Down-is-prop (m , a , ⟦ i ⟧)

 label : ℕ → (Fin n → ℕ) → Fin n → 𝟚
 label m a i = label-bit (ℕ-is-discrete (a i) (succ (side m)))
                         (ℕ-is-discrete (a i) 0)
                         (moves-down-decision m a i)

\end{code}

L1: the labels on the faces, in the form of the hypotheses of
Kuhn-Lemma n.

\begin{code}

 labels-on-lower-faces : (m : ℕ) (a : Fin n → ℕ)
                       → ((j : Fin n) → a j ≤ succ (side m))
                       → (i : Fin n) → a i ＝ 0 → label m a i ＝ ₀
 labels-on-lower-faces m a _ i e =
  label-bit-of-second (ℕ-is-discrete (a i) (succ (side m)))
   (ℕ-is-discrete (a i) 0)
   (moves-down-decision m a i) (λ e' → positive-not-zero (side m) (e' ⁻¹ ∙ e)) e

 labels-on-upper-faces : (m : ℕ) (a : Fin n → ℕ)
                       → ((j : Fin n) → a j ≤ succ (side m))
                       → (i : Fin n) → a i ＝ succ (side m) → label m a i ＝ ₁
 labels-on-upper-faces m a _ i e =
  label-bit-of-first (ℕ-is-discrete (a i) (succ (side m)))
   (ℕ-is-discrete (a i) 0)
   (moves-down-decision m a i) e

\end{code}

L2: the two inequalities, if F takes values in the cube.

\begin{code}

 module _ (F-in-cube : (v : ℝ^ n) → in-cube (F v)) where

  label-₀-gives-below : (m : ℕ) (a : Fin n → ℕ) (i : Fin n)
                      → label m a i ＝ ₀
                      → ι (grid-point m a i)
                      ≤ F (rational-point (grid-point m a)) i
  label-₀-gives-below m a i e =
   γ (label-bit-₀ (ℕ-is-discrete (a i) (succ (side m))) (ℕ-is-discrete (a i) 0)
       (moves-down-decision m a i) e)
   where
    v : ℝ^ n
    v = rational-point (grid-point m a)

    γ : (a i ＝ 0) ∔ ¬ Moves-Down (m , a , ⟦ i ⟧) → ι (grid-point m a i) ≤ F v i
    γ (inl e₀) =
     transport (λ - → ι - ≤ F v i) (grid-point-on-lower-face m a i e₀ ⁻¹)
                  (pr₁ (F-in-cube v i))
    γ (inr ν)  = ℝ-not-less-is-greater-or-equal (F v i) (ι (grid-point m a i))
                  (λ o → ν (i , refl , o))

  label-₁-gives-above : (m : ℕ) (a : Fin n → ℕ) (i : Fin n)
                      → label m a i ＝ ₁
                      → F (rational-point (grid-point m a)) i
                      ≤ ι (grid-point m a i)
  label-₁-gives-above m a i e =
   γ (label-bit-₁ (ℕ-is-discrete (a i) (succ (side m))) (ℕ-is-discrete (a i) 0)
       (moves-down-decision m a i) e)
   where
    v : ℝ^ n
    v = rational-point (grid-point m a)

    γ : (a i ＝ succ (side m)) ∔ Moves-Down (m , a , ⟦ i ⟧)
      → F v i ≤ ι (grid-point m a i)
    γ (inl e₁)           =
     transport (λ - → F v i ≤ ι -) (grid-point-on-upper-face m a i e₁ ⁻¹)
                            (pr₂ (F-in-cube v i))
    γ (inr (j , d , o)) =
     transport (λ - → F v - ≤ ι (grid-point m a -)) (⟦_⟧-lc n d)
                           (ℝ<-gives-≤ (F v j) (ι (grid-point m a j)) o)

\end{code}
