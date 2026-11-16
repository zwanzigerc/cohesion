Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 12 November 2026. See the AI disclosure in
gist.RealCohesion.index.

The crisp fixed point on the cube: Corollary 3.7 of the write-up [1],
cube form, gate G11 of Claude Fable 5.2's blueprint addendum [2, §§5.4,
5.6 and 5.7].

The exact statement. Corollary 3.7: assume crisp excluded middle and
Axiom R♭, let n ≥ 1 be crisp and Dⁿ the Euclidean unit ball; every
crisp f : Dⁿ → Dⁿ has a fixed point, and every f : Dⁿ → Dⁿ satisfies
♯ ∃ x , f x ＝ x.

The formal statement, crisp-cube-fixed-point, is the crisp half for
the cube [-1,1]ⁿ in place of Dⁿ, for every crisp n, relative to
Kuhn's lemma in dimension n, which is a crisp hypothesis. Kuhn's lemma
and the corners of unit cubes are taken from gist.RealCohesion.KuhnLemma,
whose definitions do not depend on module parameters (see
gist.RealCohesion.RationalGrid for why that matters here). In
gist.RealCohesion.Theorems the theorem is stated from Axiom R♭ with the
types of gist.RealCohesion.BrouwerStatements (Target-3-7-crisp), with
the ♯ half (Target-3-7-sharp), and in dimensions 0 and 1 with Kuhn's
lemma discharged. The bridge to the exact statement is
crisp-retracts-of-the-cube-have-fixed-points and
retracts-of-the-cube-have-sharp-fixed-points of
gist.RealCohesion.BrouwerStatements: both forms hold for every crisp
retract of the cube, and the exact statement is the instance Dⁿ. Still
missing for it: Dⁿ with its retraction, which needs multiplication,
square roots and division of real numbers, and Kuhn's lemma for
general n; both are gate G14.

The proof is the write-up's, in the form of the addendum.

 * For each level m, Kuhn's lemma applied to the labels of
   gist.RealCohesion.CubeGrid gives a unit cube of the grid with base
   corner U m and, for every coordinate i, a corner whose i-th label
   is ₀ and one whose i-th label is ₁. By the two inequalities of the
   labels, F moves the i-th coordinate up at the first, or leaves it,
   and down at the second, or leaves it.

 * The base corners form a crisp sequence of rational points of the
   cube. Bolzano–Weierstrass (gist.RealCohesion.CrispBolzanoWeierstrass)
   gives a point x of the cube and indices μ along which U converges
   to x with modulus 2⁻ʲ.

 * The corners differ from the base corner by at most one mesh,
   2^(1-m), so along the indices μ (j + 2) each family of corners
   converges to x with modulus 2⁻ʲ.

 * Closed half-lines are sequentially closed, from the constancy of
   maps ℝ → Q (gist.RealCohesion.FunctionalHitting), applied to
   v ↦ v i - F v i and to v ↦ F v i - v i, give x i ≤ F x i and
   F x i ≤ x i. So F x ＝ x.

 * A crisp f : Cube n → Cube n gives the crisp map F v = f (clamp v)
   from ℝⁿ to the cube, and a fixed point of F is a fixed point of f.

Only crisp excluded middle for propositions in 𝓤₀ is used, for the
labels and in Bolzano–Weierstrass, and the constancy of maps ℝ → Q,
which follows from Axiom R♭, only in the fourth step, where no
crispness is needed. Neither univalence nor Axiom T is used.

[1] Answers to some open problems in real-cohesive homotopy type
    theory. Research notes, seventh revision of 11 November 2026,
    Corollary 3.7 and its proof.
    references/C03-write-up-2026-11-11-seventh.tex
    references/C03a-write-up-seventh-README.txt

[2] Claude Fable 5.2. Formalization blueprint, addendum, revision 4 of
    11 November 2026.
    references/F14-brouwer-addendum-rev4.md

\begin{code}

{-# OPTIONS --safe --without-K --cohesion #-}

open import MLTT.Spartan renaming (_+_ to _∔_)
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons
open import gist.CohesiveApartness.Flat

module gist.RealCohesion.CubeFixedPoint
        (@♭ fe : Fun-Ext)
        (@♭ pe : Prop-Ext)
        (@♭ pt : propositional-truncations-exist)
       where

open import Fin.Type
open import Naturals.Addition renaming (_+_ to _+ℕ_)
open import Naturals.Order
open import Notation.CanonicalMap
open import Notation.Order
open import Rationals.Addition renaming (_+_ to _ℚ+_)
open import Rationals.Order
open import Rationals.Type
open import Rationals.Limits fe pe pt using (⟨1/2⟩^_)
open import UF.Subsingletons-FunExt using (Π-is-prop)
open import DedekindReals.Order fe pe pt
open import DedekindReals.Type fe pe pt
open import gist.RealCohesion.BrouwerStatements fe pe pt
 using (ℝ^ ; in-cube ; Cube ; rational-point ; _is-within-2⁻_of_ ;
         Crisp-Cube-Fixed-Point)
open import gist.RealCohesion.CrispBolzanoWeierstrass fe pe pt
 using (half-of-two ; half-of-power ; limit-point ; indices ; indices-grow ;
        indices-converge)
open import gist.RealCohesion.CubeGrid fe pe pt
 using (grid-points-are-in-cube ; label ; labels-on-lower-faces ;
         labels-on-upper-faces ;
        label-₀-gives-below ; label-₁-gives-above)
open import gist.RealCohesion.FiniteChainQuotient fe pe pt using (Q)
open import gist.RealCohesion.KuhnLemma using (bit ; corner ; Kuhn-Lemma)
open import gist.RealCohesion.FunctionalHitting fe pe pt
 using (closed-half-lines-are-sequentially-closed)
open import gist.RealCohesion.RationalArithmetic
 using (half ; halves-add-up ; two ; two-is-nonneg ; minus-one-plus-two ; mult ;
         mult-add ;
        mult-nonneg ; mult-mono ; mult-one)
open import gist.RealCohesion.RationalGrid
 using
  (side ; mesh ; mesh-is-nonneg ; mesh-antitone ; grid-point ; grid-point-is)
open import gist.RealCohesion.RationalPoints fe pe pt using (ιₐ ; ιₐ-is-ι)
open import gist.RealCohesion.RealLattice fe pe pt
 using (ιₐ-≤-ιₐ ; clamp ; clamp-inside ; clamp-is-above-lo ; clamp-is-below-hi ;
        difference-of-≤ ; ≤-from-difference)
 renaming (_+_ to _ℝ+_ ; -_ to ℝ-_)
open import gist.RealCohesion.RealLimits fe pe pt
 using
  (ρ-decreases ; within ; within-trans ; within-weaken ; within-in-interval)
open import gist.RealCohesion.RealOrder fe pe pt using (embedding-preserves-≤)
open import gist.RealCohesion.SequentialHitting fe pe pt
 using (within-from-starter-bounds ; starter-bounds-from-within)

open PropositionalTruncation pt

\end{code}

Rational facts. The mesh 2^(1-m) of the grid is a power of 1/2 from
level 1 on, and at level m ≥ j + 2 one mesh and 2⁻⁽ʲ⁺²⁾ together are
at most 2⁻ʲ.

\begin{code}

mesh-is-power : (j : ℕ) → mesh (succ j) ＝ ⟨1/2⟩^ j
mesh-is-power 0        = half-of-two
mesh-is-power (succ j) = ap half (mesh-is-power j) ∙ half-of-power j

power-doubled : (j : ℕ) → (⟨1/2⟩^ (succ j)) ℚ+ (⟨1/2⟩^ (succ j)) ＝ ⟨1/2⟩^ j
power-doubled j =
 ap (λ w → w ℚ+ w) (half-of-power j ⁻¹) ∙ halves-add-up (⟨1/2⟩^ j)

grid-steps-shrink : (j m : ℕ) → succ (succ j) ≤ m
                  → mesh m ℚ+ (⟨1/2⟩^ (succ (succ j))) ≤ (⟨1/2⟩^ j)
grid-steps-shrink j m l =
 transport (mesh m ℚ+ (⟨1/2⟩^ (succ (succ j))) ≤_) (power-doubled j)
  (ℚ≤-adding (mesh m) (⟨1/2⟩^ (succ j)) (⟨1/2⟩^ (succ (succ j)))
    (⟨1/2⟩^ (succ j))
    (transport (mesh m ≤_) (mesh-is-power (succ j))
      (mesh-antitone (succ (succ j)) m l))
    (ℚ<-coarser-than-≤ (⟨1/2⟩^ (succ (succ j))) (⟨1/2⟩^ (succ j))
      (ρ-decreases j)))

\end{code}

A corner of the unit cube at q differs from q by at most one mesh in
every coordinate.

\begin{code}

bit-is-at-most-one : (c : 𝟚) → bit c ≤ 1
bit-is-at-most-one ₀ = ⋆
bit-is-at-most-one ₁ = ⋆

corner-is-a-step-away
 : {n : ℕ} (m : ℕ) (q : Fin n → ℕ) (r : Fin n → 𝟚) (k : Fin n)
                      → grid-point m (corner q r) k
                        ＝ grid-point m q k ℚ+ mult (mesh m) (bit (r k))
corner-is-a-step-away m q r k =
   grid-point-is m (corner q r) k
 ∙ ap (-1ℚ ℚ+_) (mult-add (mesh m) (q k) (bit (r k)))
 ∙ ℚ+-assoc -1ℚ (mult (mesh m) (q k)) (mult (mesh m) (bit (r k))) ⁻¹
 ∙ ap (_ℚ+ mult (mesh m) (bit (r k))) (grid-point-is m q k ⁻¹)

corner-bounds : {n : ℕ} (m : ℕ) (q : Fin n → ℕ) (r : Fin n → 𝟚) (k : Fin n)
              → (grid-point m q k ≤ grid-point m (corner q r) k)
              × (grid-point m (corner q r) k ≤ grid-point m q k ℚ+ mesh m)
corner-bounds m q r k =
 transport (grid-point m q k ≤_) (e ⁻¹)
  (ℚ≤-addition-preserves-order'' (grid-point m q k) t
    (mult-nonneg (mesh m) (mesh-is-nonneg m) (bit (r k)))) ,
 transport (_≤ grid-point m q k ℚ+ mesh m) (e ⁻¹)
  (ℚ≤-addition-preserves-order-left t (mesh m) (grid-point m q k)
    (transport (t ≤_) (mult-one (mesh m))
      (mult-mono (mesh m) (mesh-is-nonneg m) (bit (r k)) 1
        (bit-is-at-most-one (r k)))))
 where
  t : ℚ
  t = mult (mesh m) (bit (r k))

  e : grid-point m (corner q r) k ＝ grid-point m q k ℚ+ t
  e = corner-is-a-step-away m q r k

embedding-above : (l y : ℚ) → l ≤ y → ιₐ l ≤ ι y
embedding-above l y h = transport (ιₐ l ≤_) (ιₐ-is-ι y) (ιₐ-≤-ιₐ l y h)

embedding-below : (y r : ℚ) → y ≤ r → ι y ≤ ιₐ r
embedding-below y r h = transport (_≤ ιₐ r) (ιₐ-is-ι y) (ιₐ-≤-ιₐ y r h)

corner-within-mesh : {n : ℕ} (m : ℕ) (q : Fin n → ℕ) (r : Fin n → 𝟚) (k : Fin n)
                   → within (mesh m) (ι (grid-point m (corner q r) k))
                      (ι (grid-point m q k))
corner-within-mesh m q r k =
 within-in-interval (mesh m) u (u ℚ+ mesh m) (ι (grid-point m (corner q r) k))
  (ι u)
  (ℚ≤-refl (u ℚ+ mesh m))
  (embedding-above u (grid-point m (corner q r) k) (pr₁ b))
  (embedding-below (grid-point m (corner q r) k) (u ℚ+ mesh m) (pr₂ b))
  (embedding-above u u (ℚ≤-refl u))
  (embedding-below u (u ℚ+ mesh m)
    (ℚ≤-addition-preserves-order'' u (mesh m) (mesh-is-nonneg m)))
 where
  u : ℚ
  u = grid-point m q k

  b : (u ≤ grid-point m (corner q r) k)
    × (grid-point m (corner q r) k ≤ u ℚ+ mesh m)
  b = corner-bounds m q r k

\end{code}

The function form, §5.4 and §5.6 of the addendum: crisp excluded
middle, Kuhn's lemma in dimension n and a map F : ℝⁿ → ℝⁿ, all crisp.
First the corner sequences and their limit, which need no further
hypothesis.

\begin{code}

module function-form
        (@♭ cem : Crisp-EM 𝓤₀)
        {@♭ n : ℕ}
        (@♭ kuhn : Kuhn-Lemma n)
        (@♭ F : ℝ^ n → ℝ^ n)
       where

 kuhn-cube : (m : ℕ)
           → Σ q ꞉ (Fin n → ℕ) , ((i : Fin n) → q i ≤ side m)
             × ((i : Fin n) → Σ r ꞉ (Fin n → 𝟚) , Σ s ꞉ (Fin n → 𝟚)
                 , (label cem F m (corner q r) i ＝ ₀)
                 × (label cem F m (corner q s) i ＝ ₁))
 kuhn-cube m = kuhn (side m) (label cem F m)
                (labels-on-lower-faces cem F m) (labels-on-upper-faces cem F m)

 base : ℕ → Fin n → ℕ
 base m = pr₁ (kuhn-cube m)

 base-in-range : (m : ℕ) (i : Fin n) → base m i ≤ succ (side m)
 base-in-range m i = ≤-trans (base m i) (side m) (succ (side m))
                      (pr₁ (pr₂ (kuhn-cube m)) i) (≤-succ (side m))

 lower-corner upper-corner : ℕ → Fin n → Fin n → 𝟚
 lower-corner m i = pr₁ (pr₂ (pr₂ (kuhn-cube m)) i)
 upper-corner m i = pr₁ (pr₂ (pr₂ (pr₂ (kuhn-cube m)) i))

 lower-label : (m : ℕ) (i : Fin n)
             → label cem F m (corner (base m) (lower-corner m i)) i ＝ ₀
 lower-label m i = pr₁ (pr₂ (pr₂ (pr₂ (pr₂ (kuhn-cube m)) i)))

 upper-label : (m : ℕ) (i : Fin n)
             → label cem F m (corner (base m) (upper-corner m i)) i ＝ ₁
 upper-label m i = pr₂ (pr₂ (pr₂ (pr₂ (pr₂ (kuhn-cube m)) i)))

\end{code}

The base corners U m of the unit cubes, and their limit, with the data
that the proof of Theorem 4.3 will use (§5.6, C5, of the addendum).
The sequence U is abstract, with its defining equation U-is: otherwise
Agda unfolds it when it compares types that mention the lemmas of
gist.RealCohesion.CrispBolzanoWeierstrass, and checking this module
did not finish in two minutes, instead of taking seconds.

\begin{code}

 abstract
  U : ℕ → Fin n → ℚ
  U m = grid-point m (base m)

  U-is : (m : ℕ) → U m ＝ grid-point m (base m)
  U-is m = refl

  U-in-cube : (m : ℕ) → in-cube (rational-point (U m))
  U-in-cube m = grid-points-are-in-cube m (base m) (base-in-range m)

  corners-are-near-the-base : (m : ℕ) (r : Fin n → 𝟚) (k : Fin n)
                            → within (mesh m)
                               (ι (grid-point m (corner (base m) r) k))
                                     (ι (U m k))
  corners-are-near-the-base m r k = corner-within-mesh m (base m) r k

 x : ℝ^ n
 x = limit-point cem U

 μ : ℕ → ℕ
 μ = indices cem U U-in-cube

 μ-grows : (j : ℕ) → j ≤ μ j
 μ-grows = indices-grow cem U U-in-cube

 base-corners-converge : (j : ℕ) → rational-point (U (μ j)) is-within-2⁻ j of x
 base-corners-converge = indices-converge cem U U-in-cube

 grid-points-converge
  : (j : ℕ) → rational-point (grid-point (μ j) (base (μ j))) is-within-2⁻ j of x
 grid-points-converge j = transport (λ P → rational-point P is-within-2⁻ j of x)
                           (U-is (μ j)) (base-corners-converge j)

\end{code}

Along μ (j + 2), every family of corners converges to x with modulus
2⁻ʲ: a corner is within one mesh of the base corner, and one mesh and
2⁻⁽ʲ⁺²⁾ together are at most 2⁻ʲ.

\begin{code}

 corners-are-near-the-limit
  : (j m : ℕ) → succ (succ j) ≤ m
  → rational-point (U m) is-within-2⁻ (succ (succ j)) of x
  → (r : Fin n → 𝟚) (k : Fin n)
  → within (⟨1/2⟩^ j) (ι (grid-point m (corner (base m) r) k)) (x k)
 corners-are-near-the-limit j m l u r k =
  within-weaken (mesh m ℚ+ (⟨1/2⟩^ (succ (succ j)))) (⟨1/2⟩^ j)
   (ι (grid-point m (corner (base m) r) k)) (x k)
   (grid-steps-shrink j m l)
   (within-trans (mesh m) (⟨1/2⟩^ (succ (succ j)))
     (ι (grid-point m (corner (base m) r) k)) (ι (U m k)) (x k)
     (corners-are-near-the-base m r k)
     (within-from-starter-bounds (succ (succ j)) (ι (U m k)) (x k) (pr₁ (u k))
       (pr₂ (u k))))

 corner-converges
  : (c : ℕ → Fin n → 𝟚) (j : ℕ)
  → rational-point (grid-point (μ (succ (succ j)))
                     (corner (base (μ (succ (succ j))))
                       (c (μ (succ (succ j))))))
     is-within-2⁻ j of x
 corner-converges c j k =
  starter-bounds-from-within j
   (ι (grid-point (μ (succ (succ j)))
        (corner (base (μ (succ (succ j)))) (c (μ (succ (succ j)))))
        k))
   (x k)
   (corners-are-near-the-limit j (μ (succ (succ j))) (μ-grows (succ (succ j)))
     (base-corners-converge (succ (succ j))) (c (μ (succ (succ j)))) k)

\end{code}

The limit is a fixed point, if maps ℝ → Q are constant and F takes
values in the cube.

\begin{code}

 module _ (ν : (k : ℝ → Q) (u v : ℝ) → k u ＝ k v)
          (F-in-cube : (v : ℝ^ n) → in-cube (F v))
        where

  below-at-lower-corners
   : (m : ℕ) (i : Fin n)
   → rational-point (grid-point m (corner (base m) (lower-corner m i))) i
      ℝ+ (ℝ- F
        (rational-point (grid-point m (corner (base m) (lower-corner m i)))) i)
     ≤ 0ℝ
  below-at-lower-corners m i =
   difference-of-≤
    (rational-point (grid-point m (corner (base m) (lower-corner m i))) i)
    (F (rational-point (grid-point m (corner (base m) (lower-corner m i)))) i)
    (label-₀-gives-below cem F F-in-cube m (corner (base m) (lower-corner m i))
      i
      (lower-label m i))

  above-at-upper-corners
   : (m : ℕ) (i : Fin n)
   → F (rational-point (grid-point m (corner (base m) (upper-corner m i)))) i
      ℝ+
       (ℝ- rational-point (grid-point m (corner (base m) (upper-corner m i))) i)
     ≤ 0ℝ
  above-at-upper-corners m i =
   difference-of-≤
    (F (rational-point (grid-point m (corner (base m) (upper-corner m i)))) i)
    (rational-point (grid-point m (corner (base m) (upper-corner m i))) i)
    (label-₁-gives-above cem F F-in-cube m (corner (base m) (upper-corner m i))
      i
      (upper-label m i))

  x-is-below-its-image : (i : Fin n) → x i ≤ F x i
  x-is-below-its-image i =
   ≤-from-difference (x i) (F x i)
    (closed-half-lines-are-sequentially-closed ν (Fin n)
      (λ v → v i ℝ+ (ℝ- F v i)) x
      (λ j → rational-point (grid-point (μ (succ (succ j)))
                               (corner (base (μ (succ (succ j))))
                                 (lower-corner (μ (succ (succ j))) i))))
      (corner-converges (λ m → lower-corner m i))
      (λ j → below-at-lower-corners (μ (succ (succ j))) i))

  image-is-below-x : (i : Fin n) → F x i ≤ x i
  image-is-below-x i =
   ≤-from-difference (F x i) (x i)
    (closed-half-lines-are-sequentially-closed ν (Fin n)
      (λ v → F v i ℝ+ (ℝ- v i)) x
      (λ j → rational-point (grid-point (μ (succ (succ j)))
                               (corner (base (μ (succ (succ j))))
                                 (upper-corner (μ (succ (succ j))) i))))
      (corner-converges (λ m → upper-corner m i))
      (λ j → above-at-upper-corners (μ (succ (succ j))) i))

  x-is-fixed : F x ＝ x
  x-is-fixed =
   dfunext fe (λ i → ≤-ℝ-ℝ-antisym (F x i) (x i) (image-is-below-x i)
                        (x-is-below-its-image i))

  fixed-point : Σ y ꞉ ℝ^ n , F y ＝ y
  fixed-point = x , x-is-fixed

\end{code}

From self-maps of the cube to maps from ℝⁿ to the cube, §5.7 of the
addendum: clamp every coordinate to [-1,1], then apply f. On the cube
the composite agrees with f, and a fixed point of the composite lies
in the cube and is a fixed point of f.

\begin{code}

minus-one-below-one : ι -1ℚ ≤ 1ℝ
minus-one-below-one =
 embedding-preserves-≤ -1ℚ 1ℚ
  (transport (-1ℚ ≤_) minus-one-plus-two
    (ℚ≤-addition-preserves-order'' -1ℚ two two-is-nonneg))

module _ {n : ℕ} where

 clamp-to-cube : ℝ^ n → ℝ^ n
 clamp-to-cube v i = clamp (ι -1ℚ) 1ℝ (v i)

 clamp-is-in-cube : (v : ℝ^ n) → in-cube (clamp-to-cube v)
 clamp-is-in-cube v i = clamp-is-above-lo (ι -1ℚ) 1ℝ (v i) ,
                        clamp-is-below-hi (ι -1ℚ) 1ℝ (v i) minus-one-below-one

 clamp-fixes-the-cube : (v : ℝ^ n) → in-cube v → clamp-to-cube v ＝ v
 clamp-fixes-the-cube v c =
  dfunext fe (λ i → clamp-inside (ι -1ℚ) 1ℝ (v i) (pr₁ (c i)) (pr₂ (c i)))

 being-in-the-cube-is-prop : (v : ℝ^ n) → is-prop (in-cube v)
 being-in-the-cube-is-prop v =
  Π-is-prop fe (λ i → ×-is-prop (≤-is-prop (ι -1ℚ) (v i)) (≤-is-prop (v i) 1ℝ))

 on-ℝ^ : (Cube n → Cube n) → ℝ^ n → ℝ^ n
 on-ℝ^ f v = pr₁ (f (clamp-to-cube v , clamp-is-in-cube v))

 on-ℝ^-is-in-cube : (f : Cube n → Cube n) (v : ℝ^ n) → in-cube (on-ℝ^ f v)
 on-ℝ^-is-in-cube f v = pr₂ (f (clamp-to-cube v , clamp-is-in-cube v))

 on-ℝ^-agrees : (f : Cube n → Cube n) (v : ℝ^ n) (c : in-cube v)
              → on-ℝ^ f v ＝ pr₁ (f (v , c))
 on-ℝ^-agrees f v c =
  ap (λ w → pr₁ (f w))
   (to-subtype-＝ being-in-the-cube-is-prop (clamp-fixes-the-cube v c))

 fixed-points-on-ℝ^ : (f : Cube n → Cube n) (y : ℝ^ n)
                    → on-ℝ^ f y ＝ y → Σ c ꞉ in-cube y , f (y , c) ＝ (y , c)
 fixed-points-on-ℝ^ f y e =
  c , to-subtype-＝ being-in-the-cube-is-prop (on-ℝ^-agrees f y c ⁻¹ ∙ e)
  where
   c : in-cube y
   c = transport in-cube e (on-ℝ^-is-in-cube f y)

\end{code}

The theorem, for the cube in dimension n, relative to Kuhn's lemma in
dimension n.

\begin{code}

crisp-cube-fixed-point : (@♭ cem : Crisp-EM 𝓤₀)
                       → ((k : ℝ → Q) (u v : ℝ) → k u ＝ k v)
                       → {@♭ n : ℕ} (@♭ kuhn : Kuhn-Lemma n)
                       → Crisp-Cube-Fixed-Point n
crisp-cube-fixed-point cem ν {n} kuhn f = ∣ (pr₁ s , pr₁ t) , pr₂ t ∣
 where
  s : Σ y ꞉ ℝ^ n , on-ℝ^ f y ＝ y
  s = function-form.fixed-point cem kuhn (on-ℝ^ f) ν (on-ℝ^-is-in-cube f)

  t : Σ c ꞉ in-cube (pr₁ s) , f (pr₁ s , c) ＝ (pr₁ s , c)
  t = fixed-points-on-ℝ^ f (pr₁ s) (pr₂ s)

\end{code}
