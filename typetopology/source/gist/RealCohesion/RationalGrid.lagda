Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. See the AI disclosure in
gist.RealCohesion.index.

The rational grid of the cube [-1,1]ⁿ, for the proof of Corollary 3.7
of the write-up [1] in the cube form of Claude Fable 5.2's blueprint
addendum [2, §5.2]. At level m the side has 2^m steps of length
2^(1-m), the mesh, and the grid point with index a : Fin n → ℕ is the
rational point with coordinates -1 + 2^(1-m) · a i. These are the
rational parts of gist.RealCohesion.CubeGrid, which re-exports them.

The side 2^m is succ (side m), without subtraction, and the mesh is a
halving sequence. Grid points are abstract, with their defining
equation grid-point-is: otherwise comparisons of real numbers at grid
points unfold the rational arithmetic inside the cuts, and
gist.RealCohesion.CubeGrid took more than ten minutes to check
instead of two seconds.

This module has no parameters, unlike gist.RealCohesion.CubeGrid.
When grid points depended on the parameter fe : Fun-Ext of that
module, Agda took minutes to compare real numbers at grid points
stated in different places, even where they were written the same
way; without the parameter the same comparisons take seconds. The
parameter has implicit arguments, and its occurrences need not be
elaborated to the same term.

[1] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, seventh revision of 11 November 2026,
    proof of Corollary 3.7, paragraph "Labels".
    references/C03-write-up-2026-11-11-seventh.tex
    references/C03a-write-up-seventh-README.txt

[2] Claude Fable 5.2. Formalization blueprint, addendum, revision 4 of
    11 November 2026, §5.2.
    references/F14-brouwer-addendum-rev4.md

\begin{code}

{-# OPTIONS --safe --without-K #-}

module gist.RealCohesion.RationalGrid where

open import MLTT.Spartan renaming (_+_ to _∔_)
open import Fin.Type
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Naturals.Order
open import Notation.Order
open import Rationals.Addition
open import Rationals.Order
open import Rationals.Type
open import gist.RealCohesion.RationalArithmetic
 using
  (half ; two ; two-is-nonneg ; minus-one-plus-two ; module halving-sequence ;
   mult ; mult-zero ; mult-nonneg ; mult-mono ; mult-one ; mult-half)

\end{code}

The grid of level m: side 2^m = succ (side m) and mesh 2^(1-m), a
halving sequence. The mesh fills the side of the cube: 2^m steps of
2^(1-m) make 2.

\begin{code}

side : ℕ → ℕ
side 0        = 0
side (succ m) = succ (side m) +ℕ side m

mesh : ℕ → ℚ
mesh m = rec two half m

mesh-is-nonneg : (m : ℕ) → 0ℚ ≤ mesh m
mesh-is-nonneg =
 halving-sequence.nonneg.is-nonneg mesh (λ m → refl) two-is-nonneg

mesh-antitone : (j k : ℕ) → j ≤ℕ k → mesh k ≤ mesh j
mesh-antitone = halving-sequence.nonneg.antitone mesh (λ m → refl) two-is-nonneg

mesh-fills-the-side : (m : ℕ) → mult (mesh m) (succ (side m)) ＝ two
mesh-fills-the-side 0        = mult-one two
mesh-fills-the-side (succ m) =
 mult-half (mesh m) (succ (side m)) ∙ mesh-fills-the-side m

\end{code}

Grid points, and the facts about them that use their definition: the
two faces, and the bounds of the cube in range.

\begin{code}

abstract
 grid-point : {n : ℕ} → ℕ → (Fin n → ℕ) → Fin n → ℚ
 grid-point m a i = -1ℚ + mult (mesh m) (a i)

 grid-point-is : {n : ℕ} (m : ℕ) (a : Fin n → ℕ) (i : Fin n)
               → grid-point m a i ＝ -1ℚ + mult (mesh m) (a i)
 grid-point-is m a i = refl

 grid-point-on-lower-face : {n : ℕ} (m : ℕ) (a : Fin n → ℕ) (i : Fin n)
                          → a i ＝ 0 → grid-point m a i ＝ -1ℚ
 grid-point-on-lower-face m a i e =
  ap (λ k → -1ℚ + mult (mesh m) k) e
  ∙ ap (-1ℚ +_) (mult-zero (mesh m))
  ∙ ℚ-zero-right-neutral -1ℚ

 grid-point-on-upper-face : {n : ℕ} (m : ℕ) (a : Fin n → ℕ) (i : Fin n)
                          → a i ＝ succ (side m) → grid-point m a i ＝ 1ℚ
 grid-point-on-upper-face m a i e =
  ap (λ k → -1ℚ + mult (mesh m) k) e
  ∙ ap (-1ℚ +_) (mesh-fills-the-side m)
  ∙ minus-one-plus-two

 grid-point-bounds : {n : ℕ} (m : ℕ) (a : Fin n → ℕ)
                   → ((i : Fin n) → a i ≤ succ (side m))
                   → (i : Fin n)
                   → (-1ℚ ≤ grid-point m a i) × (grid-point m a i ≤ 1ℚ)
 grid-point-bounds m a l i = I , II
  where
   I : -1ℚ ≤ grid-point m a i
   I = ℚ≤-addition-preserves-order'' -1ℚ (mult (mesh m) (a i))
        (mult-nonneg (mesh m) (mesh-is-nonneg m) (a i))

   II : grid-point m a i ≤ 1ℚ
   II = transport (grid-point m a i ≤_)
         (ap (-1ℚ +_) (mesh-fills-the-side m) ∙ minus-one-plus-two)
         (ℚ≤-addition-preserves-order-left (mult (mesh m) (a i))
           (mult (mesh m) (succ (side m))) -1ℚ
           (mult-mono (mesh m) (mesh-is-nonneg m) (a i) (succ (side m)) (l i)))

\end{code}
