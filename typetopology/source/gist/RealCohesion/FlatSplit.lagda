Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 and 26 October 2026; the restatements for nLab problem 4,
for nLab problem 1 without its continuity hypothesis, and without
Axiom T added 10 November 2026; those for rational detection and for
Shulman's Corollary 11.6 added 11 November 2026; Constancy and
Constancy-is-prop made typed aliases of gist.RealCohesion.Constancy,
13 November 2026, in the consolidation after the final audits; the
constancy from Axiom C1 and a merely strictly rising generator path,
and the approximate intermediate value theorem with a rational witness
from it, added the same day in the second part of the consolidation
(Section 4.4 of Claude Fable 5.2's consolidation plan, released by
GPT-6 Astra). See the AI disclosure in gist.RealCohesion.index.

Crisp pattern matching.

This module uses Agda's --flat-split, which allows pattern matching on
crisp variables of inductive types, here crisp elements of identity
types and crisp natural numbers. This is crisp induction in the sense
of Shulman [1, §5]. Agda does not allow --flat-split together with
--safe and --without-K, so this module is not --safe, unlike the
others in this folder, which take the consequences of crisp induction
that they need as hypotheses.

We prove the three such consequences used in this folder:

 * the constructor of ♭ respects crisp identifications, which is the
   decoding half of Shulman's characterization of the identity types
   of ♭ A [1, Theorem 6.1];

 * ℕ is ♭-discrete, which reduces countable choice for crisp families
   to Shulman's discrete axiom of choice [1, Theorem 6.30];

 * ♭ A is ♭-discrete for every crisp type A, part of Shulman's proof
   that ♭ is a coreflector onto the discrete types [1, §6.2].

We then instantiate gist.RealCohesion.CrispDiscreteness, so that its
results hold assuming only the axioms named in their statements, and
gist.RealCohesion.RealShapeContinuity with the discrete axiom of choice
in place of countable choice for crisp families. (That 𝟚 is
♭-discrete, the other consequence of crisp induction used here and in
gist.CohesiveApartness, is proved in gist.CohesiveApartness.FlatSplit.)
We instantiate the refutation of gist.RealCohesion.RealSubsetShape
with the ♭-discreteness of 𝟚, for nLab problem 1, and restate it
without its continuity hypothesis, which follows from crisp excluded
middle and Axiom R♭ (gist.RealCohesion.CrispContinuity). We
instantiate gist.RealCohesion.ApproximateIVT with crisp-ap-^♭ and the
♭-discreteness of 𝟚, which gives the approximate intermediate value
theorem for arbitrary functions from Axiom R♭ alone, for nLab
problem 4. We state the continuity of crisp functions at crisp points
and Shulman's Theorem 11.2 for crisp witnesses from crisp excluded
middle and Axiom R♭, without Axiom T. We state GPT-6 Astra's rational
detection and the approximate intermediate value theorem with a
rational witness from Axiom R♭ alone, and, with crisp excluded middle,
the continuity of crisp functions at all points and Shulman's Theorem
11.2 for arbitrary witnesses. Finally, we state Shulman's Corollary
11.6 without Axiom T (gist.RealCohesion.FlatRealFunctions), with the
♭-discreteness of ♭ ℝ discharged.

The proof that ℕ is ♭-discrete is a port of the proof of
is-flat-discrete-crisp-ℕ in agda-unimath [2], suggested by GPT-6
Astra: a map ℕ → ♭ ℕ defined by recursion, which is an inverse of the
counit because it sends every crisp n to n ^♭, by crisp induction.

[1] Michael Shulman. Brouwer's fixed-point theorem in real-cohesive
    homotopy type theory. Mathematical Structures in Computer
    Science 28(6), 856–941, 2018. https://arxiv.org/abs/1509.07584v3

[2] The agda-unimath library, modal-type-theory.flat-discrete-crisp-types.
    https://unimath.github.io/agda-unimath/modal-type-theory.flat-discrete-crisp-types.html
    Comparison revision, not the revision consulted:
    src/modal-type-theory/flat-discrete-crisp-types.lagda.md at commit
    75518656f287c203b41cb7f71df46e02b987a084 of
    https://github.com/UniMath/agda-unimath; see the provenance ledger
    (provenance/EXTERNAL-SOURCES-CURRENT.json).

\begin{code}

{-# OPTIONS --without-K --cohesion --flat-split #-}

module gist.RealCohesion.FlatSplit where

open import MLTT.Spartan
open import UF.DiscreteAndSeparated using (ℕ-is-set)
open import UF.Equiv
open import UF.FunExt
open import UF.PropTrunc
open import UF.Sets
open import UF.SetTrunc
open import UF.Subsingletons
open import Modal.Subuniverse
open import Quotient.Type
open import UF.Univalence
open import gist.CohesiveApartness.Flat
open import gist.CohesiveApartness.FlatSplit using (𝟚-is-♭-discrete)

crisp-ap-^♭ : {@♭ 𝓤 : Universe} {@♭ A : 𝓤 ̇ } {@♭ x y : A}
            → @♭ x ＝ y → x ^♭ ＝ y ^♭
crisp-ap-^♭ refl = refl

\end{code}

ℕ is ♭-discrete.

\begin{code}

♭-succ : ♭ ℕ → ♭ ℕ
♭-succ (n ^♭) = succ n ^♭

ℕ-to-♭ℕ : ℕ → ♭ ℕ
ℕ-to-♭ℕ 0        = 0 ^♭
ℕ-to-♭ℕ (succ n) = ♭-succ (ℕ-to-♭ℕ n)

♭-counit-after-ℕ-to-♭ℕ : (n : ℕ) → ♭-counit (ℕ-to-♭ℕ n) ＝ n
♭-counit-after-ℕ-to-♭ℕ 0        = refl
♭-counit-after-ℕ-to-♭ℕ (succ n) = γ (ℕ-to-♭ℕ n) (♭-counit-after-ℕ-to-♭ℕ n)
 where
  γ : (x : ♭ ℕ) → ♭-counit x ＝ n → ♭-counit (♭-succ x) ＝ succ n
  γ (m ^♭) p = ap succ p

ℕ-to-♭ℕ-on-crisp-naturals : (@♭ n : ℕ) → ℕ-to-♭ℕ n ＝ n ^♭
ℕ-to-♭ℕ-on-crisp-naturals 0        = refl
ℕ-to-♭ℕ-on-crisp-naturals (succ n) = ap ♭-succ (ℕ-to-♭ℕ-on-crisp-naturals n)

ℕ-to-♭ℕ-after-♭-counit : (x : ♭ ℕ) → ℕ-to-♭ℕ (♭-counit x) ＝ x
ℕ-to-♭ℕ-after-♭-counit (n ^♭) = ℕ-to-♭ℕ-on-crisp-naturals n

ℕ-is-♭-discrete : is-♭-discrete ℕ
ℕ-is-♭-discrete = qinvs-are-equivs ♭-counit
                   (ℕ-to-♭ℕ , ℕ-to-♭ℕ-after-♭-counit , ♭-counit-after-ℕ-to-♭ℕ)

\end{code}

♭ A is ♭-discrete: the counit ♭ (♭ A) → ♭ A has the inverse that sends
a ^♭ to (a ^♭) ^♭, by crisp induction on the crisp element of ♭ A
inside an element of ♭ (♭ A).

\begin{code}

♭-is-♭-discrete : {@♭ 𝓤 : Universe} {@♭ A : 𝓤 ̇ } → is-♭-discrete (♭ A)
♭-is-♭-discrete {𝓤} {A} = qinvs-are-equivs ♭-counit (σ , η , ε)
 where
  σ : ♭ A → ♭ (♭ A)
  σ (a ^♭) = (a ^♭) ^♭

  η : (w : ♭ (♭ A)) → σ (♭-counit w) ＝ w
  η ((a ^♭) ^♭) = refl

  ε : (u : ♭ A) → ♭-counit (σ u) ＝ u
  ε (a ^♭) = refl

\end{code}

The instantiations.

\begin{code}

module _ (@♭ fe : Fun-Ext)
         (@♭ pe : Prop-Ext)
         (@♭ pt : propositional-truncations-exist)
       where

 open import gist.RealCohesion.CrispDiscreteness fe pe pt crisp-ap-^♭ public
 open import gist.RealCohesion.CrispCountableChoice pt
 open import DedekindReals.Type fe pe pt

\end{code}

The discrete axiom of choice gives countable choice for crisp families,
because ℕ is a crisp ♭-discrete set.

\begin{code}

 discrete-choice-gives-crisp-countable-choice
  : {@♭ 𝓦 : Universe}
  → Discrete-Choice 𝓤₀ 𝓦
  → Crisp-Countable-Choice 𝓦
 discrete-choice-gives-crisp-countable-choice dc B e =
  dc ℕ ℕ-is-♭-discrete ℕ-is-set B e

\end{code}

The finite-height obstruction to Shulman's continuity conjecture, with
the discrete axiom of choice, which Shulman derives from his Axiom AC
[1, Theorem 6.30], in place of countable choice for crisp families.

\begin{code}

 module _ (@♭ st : set-truncations-exist)
          (@♭ sq : set-quotients-exist)
          {@♭ 𝓥 : Universe}
          (@♭ P : subuniverse 𝓤₁ 𝓥)
          (@♭ P-is-reflective : subuniverse-is-reflective P)
          (@♭ P-is-ℝ-null : (X : 𝓤₁ ̇ ) → subuniverse-contains P X
                                        ↔ is-null ℝ X)
        where

  open import gist.RealCohesion.RealShapeContinuity fe pe pt st sq
  open RealShape P P-is-reflective P-is-ℝ-null
  open PropositionalTruncation pt

  shape-continuity-fails-from-discrete-choice
   : Discrete-Choice 𝓤₀ 𝓤₁
   → Finite-Height
   → (@♭ B : ℕ → 𝓤₁ ̇ )
     (@♭ B-is-set : (n : ℕ) → is-set (B n))
     (@♭ b t : (n : ℕ) → B n)
   → @♭ ((n : ℕ) → η₀ (B n) (b n) ＝ η₀ (B n) (t n))
   → ((k : ℕ) → ∃ n ꞉ ℕ , q[ k ] (b n) ≠ q[ k ] (t n))
   → ¬ is-equiv (κ (Σ n ꞉ ℕ , B n))
  shape-continuity-fails-from-discrete-choice dc =
   shape-continuity-fails (discrete-choice-gives-crisp-countable-choice dc)

\end{code}

nLab problem 1. With the proof that 𝟚 is ♭-discrete, the shape of the
image of the dyadic function of gist.RealCohesion.DyadicOscillation, a
subtype of the Dedekind reals, is not a set, assuming standard
univalent and modal structure and the following principles, which hold
in Shulman's intended model: crisp excluded middle, the continuity of
crisp real functions at crisp points, unique Boolean real-path descent,
Axiom R♭, and that the type of two-element types is modal. See
gist.RealCohesion.RealSubsetShape for these assumptions. Unlike the
version there, these restatements also rely on Agda's --flat-split.

\begin{code}

module _ (@♭ ua : Univalence)
         (@♭ pt : propositional-truncations-exist)
       where

 open import gist.RealCohesion.RealSubsetShape ua pt
  using (fe ; pe ; dyadic-image ; dyadic-image-predicate ;
         shape-of-the-dyadic-image-is-not-a-set ;
         subsets-of-ℝ-need-not-have-set-shape ;
         crisp-subsets-of-ℝ-need-not-have-set-shape)
 open import UF.SubtypeClassifier using (Ω ; _holds)
 open import DedekindReals.Type fe pe pt using (ℝ ; 0ℝ)
 open import gist.RealCohesion.CrispRealAnalysis fe pe pt
  using (Crisp-Real-Continuity)
 open import gist.RealCohesion.RealPathDescent fe pe pt
  using (Unique-Boolean-Real-Path-Descent)

 module _ {@♭ 𝓥 : Universe}
          (@♭ P : subuniverse 𝓤₁ 𝓥)
          (@♭ P-is-reflective : subuniverse-is-reflective P)
          (@♭ P-is-ℝ-null : (X : 𝓤₁ ̇ )
           → subuniverse-contains P X ↔ is-null ℝ X)
          (@♭ cem : Crisp-EM 𝓤₁)
          (@♭ continuity : Crisp-Real-Continuity)
          (@♭ descent : Unique-Boolean-Real-Path-Descent 𝓤₁)
          (r♭ : Singly-Generated-Punctual-Cohesion ℝ 0ℝ)
        where

  open import Modal.ReflectiveSubuniverse P P-is-reflective using (○ ; is-modal)
  open import gist.RealCohesion.BooleanCocycleObstruction ua pt P
   P-is-reflective
   using (B₂)

  module _ (B₂-is-modal : is-modal B₂) where

   dyadic-image-shape-is-not-a-set : ¬ is-set (○ dyadic-image)
   dyadic-image-shape-is-not-a-set =
    shape-of-the-dyadic-image-is-not-a-set P P-is-reflective P-is-ℝ-null
     cem continuity descent r♭ 𝟚-is-♭-discrete B₂-is-modal

   not-every-subset-of-ℝ-has-a-set-as-shape
    : ¬ ((A : ℝ → Ω 𝓤₁) → is-set (○ (Σ x ꞉ ℝ , A x holds)))
   not-every-subset-of-ℝ-has-a-set-as-shape =
    subsets-of-ℝ-need-not-have-set-shape P P-is-reflective P-is-ℝ-null
     cem continuity descent r♭ 𝟚-is-♭-discrete B₂-is-modal

   not-every-crisp-subset-of-ℝ-has-a-set-as-shape
    : ¬ ((@♭ A : ℝ → Ω 𝓤₁) → is-set (○ (Σ x ꞉ ℝ , A x holds)))
   not-every-crisp-subset-of-ℝ-has-a-set-as-shape =
    crisp-subsets-of-ℝ-need-not-have-set-shape P P-is-reflective P-is-ℝ-null
     cem continuity descent r♭ 𝟚-is-♭-discrete B₂-is-modal

\end{code}

nLab problem 1 without the continuity hypothesis. The continuity of
crisp functions at crisp points, Crisp-Real-Continuity, follows from
crisp excluded middle and Axiom R♭ (gist.RealCohesion.CrispContinuity),
so the three theorems above hold without it. In
gist.RealCohesion.RealSubsetShape it is a crisp hypothesis, so we need
a crisp proof of it, whereas r♭ is an ordinary hypothesis. Under Axiom
R♭ crisp propositions are ♭-discrete, and the constancy of maps ℝ → Q,
from which the continuity follows, is a crisp proposition, so it has
a crisp proof.

\begin{code}

module _ (@♭ ua : Univalence)
         (@♭ pt : propositional-truncations-exist)
       where

 open import gist.RealCohesion.RealSubsetShape ua pt
  using (fe ; pe ; dyadic-image ;
         shape-of-the-dyadic-image-is-not-a-set ;
         subsets-of-ℝ-need-not-have-set-shape ;
         crisp-subsets-of-ℝ-need-not-have-set-shape)
 open import UF.SubtypeClassifier using (Ω ; _holds)
 open import UF.Subsingletons-FunExt using (Π₃-is-prop)
 open import DedekindReals.Type fe pe pt using (ℝ ; 0ℝ)
 open import gist.RealCohesion.RealPathDescent fe pe pt
  using (Unique-Boolean-Real-Path-Descent)
 open import gist.RealCohesion.FiniteChainQuotient fe pe pt using (Q ; Q-is-set)
 import gist.RealCohesion.FiniteChainDiscreteness fe pe pt crisp-ap-^♭ as FCD
 import gist.RealCohesion.CrispContinuity fe pe pt as CC
 import gist.RealCohesion.Constancy fe pe pt as Con

 Constancy : 𝓤₁ ̇
 Constancy = Con.Constancy

 Constancy-is-prop : is-prop Constancy
 Constancy-is-prop = Con.Constancy-is-prop

 module _ {@♭ 𝓥 : Universe}
          (@♭ P : subuniverse 𝓤₁ 𝓥)
          (@♭ P-is-reflective : subuniverse-is-reflective P)
          (@♭ P-is-ℝ-null : (X : 𝓤₁ ̇ )
           → subuniverse-contains P X ↔ is-null ℝ X)
          (@♭ cem : Crisp-EM 𝓤₁)
          (@♭ descent : Unique-Boolean-Real-Path-Descent 𝓤₁)
          (r♭ : Singly-Generated-Punctual-Cohesion ℝ 0ℝ)
        where

  open import Modal.ReflectiveSubuniverse P P-is-reflective using (○ ; is-modal)
  open import gist.RealCohesion.BooleanCocycleObstruction ua pt P
   P-is-reflective
   using (B₂)

  crisp-constancy : ♭ Constancy
  crisp-constancy = inverse ♭-counit
                     (FCD.crisp-props-are-♭-discrete r♭ 𝟚-is-♭-discrete
                       Constancy Constancy-is-prop)
                     (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete)

  module _ (B₂-is-modal : is-modal B₂) where

   dyadic-image-shape-is-not-a-set-without-continuity
    : ¬ is-set (○ dyadic-image)
   dyadic-image-shape-is-not-a-set-without-continuity = γ crisp-constancy
    where
     γ : ♭ Constancy → ¬ is-set (○ dyadic-image)
     γ (ν ^♭) =
      shape-of-the-dyadic-image-is-not-a-set P P-is-reflective P-is-ℝ-null
                 cem (CC.crisp-real-continuity cem ν) descent r♭ 𝟚-is-♭-discrete
                 B₂-is-modal

   not-every-subset-of-ℝ-has-a-set-as-shape-without-continuity
    : ¬ ((A : ℝ → Ω 𝓤₁) → is-set (○ (Σ x ꞉ ℝ , A x holds)))
   not-every-subset-of-ℝ-has-a-set-as-shape-without-continuity =
    γ crisp-constancy
    where
     γ : ♭ Constancy → ¬ ((A : ℝ → Ω 𝓤₁) → is-set (○ (Σ x ꞉ ℝ , A x holds)))
     γ (ν ^♭) =
      subsets-of-ℝ-need-not-have-set-shape P P-is-reflective P-is-ℝ-null
                 cem (CC.crisp-real-continuity cem ν) descent r♭ 𝟚-is-♭-discrete
                 B₂-is-modal

   not-every-crisp-subset-of-ℝ-has-a-set-as-shape-without-continuity
    : ¬ ((@♭ A : ℝ → Ω 𝓤₁) → is-set (○ (Σ x ꞉ ℝ , A x holds)))
   not-every-crisp-subset-of-ℝ-has-a-set-as-shape-without-continuity =
    γ crisp-constancy
    where
     γ : ♭ Constancy → ¬ ((@♭ A : ℝ → Ω 𝓤₁) → is-set (○ (Σ x ꞉ ℝ , A x holds)))
     γ (ν ^♭) =
      crisp-subsets-of-ℝ-need-not-have-set-shape P P-is-reflective P-is-ℝ-null
                 cem (CC.crisp-real-continuity cem ν) descent r♭ 𝟚-is-♭-discrete
                 B₂-is-modal

\end{code}

nLab problem 4. Crispness can be removed from Shulman's approximate
intermediate value theorem [1, Theorem 11.4] assuming only Axiom R♭,
besides function extensionality, propositional extensionality and
propositional truncations: for f : ℝ → ℝ and p q a b : ℝ, none of
them crisp, with p < q, f a < q and p < f b, there merely is x with
p < f x < q. This is Theorem E of the proof note by Claude Fable 5.2
cited in gist.RealCohesion.ApproximateIVT, which proves it from Axiom
R♭, crisp-ap-^♭ and the ♭-discreteness of 𝟚.

\begin{code}

module _ (@♭ fe : Fun-Ext)
         (@♭ pe : Prop-Ext)
         (@♭ pt : propositional-truncations-exist)
       where

 open import Notation.Order
 open import DedekindReals.Type fe pe pt using (ℝ ; 0ℝ)
 open import DedekindReals.Order fe pe pt
 import gist.RealCohesion.ApproximateIVT fe pe pt crisp-ap-^♭ as AIVT
 open PropositionalTruncation pt

 approximate-IVT
  : Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → (f : ℝ → ℝ) (p q a b : ℝ)
  → p < q
  → f a < q
  → p < f b
  → ∃ x ꞉ ℝ , (p < f x) × (f x < q)
 approximate-IVT r♭ = AIVT.approximate-IVT r♭ 𝟚-is-♭-discrete

\end{code}

Axiom T in Shulman's §11. The continuity of crisp functions at crisp
points, Crisp-Real-Continuity, and Shulman's Theorem 11.2 for crisp
witnesses, assuming only crisp excluded middle and Axiom R♭, besides
function extensionality, propositional extensionality and
propositional truncations (gist.RealCohesion.CrispContinuity and
gist.RealCohesion.CrispExactIVT, with crisp-ap-^♭ and the
♭-discreteness of 𝟚 discharged). Shulman's versions also assume
Axiom T.

\begin{code}

module _ (@♭ fe : Fun-Ext)
         (@♭ pe : Prop-Ext)
         (@♭ pt : propositional-truncations-exist)
       where

 open import Notation.Order
 open import DedekindReals.Type fe pe pt using (ℝ ; 0ℝ)
 open import DedekindReals.Order fe pe pt
 open import gist.RealCohesion.CrispRealAnalysis fe pe pt
  using (Crisp-Real-Continuity)
 open import gist.RealCohesion.FiniteChainDiscreteness fe pe pt crisp-ap-^♭
  using (maps-from-ℝ-to-Q-are-constant)
 import gist.RealCohesion.CrispContinuity fe pe pt as CC
 import gist.RealCohesion.CrispExactIVT fe pe pt as EIVT
 open PropositionalTruncation pt

 crisp-functions-are-continuous-without-T
  : (@♭ cem : Crisp-EM 𝓤₁)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → Crisp-Real-Continuity
 crisp-functions-are-continuous-without-T cem r♭ =
  CC.crisp-real-continuity cem
   (maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete)

 crisp-exact-IVT-without-T
  : (@♭ cem : Crisp-EM 𝓤₁)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → (@♭ f : ℝ → ℝ) (@♭ c a b : ℝ)
  → f a < c → c < f b
  → ∃ x ꞉ ℝ , f x ＝ c
 crisp-exact-IVT-without-T cem r♭ =
  EIVT.crisp-exact-IVT cem (maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete)

\end{code}

Rational detection and its consequences. GPT-6 Astra's rational
detection holds assuming only Axiom R♭, besides function
extensionality, propositional extensionality and propositional
truncations (gist.RealCohesion.RationalDetection). It gives the
approximate intermediate value theorem with a rational witness. With
crisp excluded middle, it also gives the continuity of crisp
functions at all points of a neighbourhood, and Shulman's Theorem
11.2 for arbitrary witnesses, both without Axiom T
(gist.RealCohesion.CrispFunctionsEverywhere). The constancy of maps
from ℝ to Q also follows from Axiom C1 for an ordinary family of
generators and a strictly rising generator path in ℝ, merely
(gist.RealCohesion.FiniteChainDiscreteness), and so does the
approximate intermediate value theorem with a rational witness; these
two forms are stated here too, so that the weakening of Axiom R♭ to C1
and NC is checked with Agda 2.8 as well
(gist.RealCohesion.TheoremsFromC1 states them and the others under
Agda 2.9).

\begin{code}

module _ (@♭ fe : Fun-Ext)
         (@♭ pe : Prop-Ext)
         (@♭ pt : propositional-truncations-exist)
       where

 open import Notation.CanonicalMap
 open import Notation.Order
 open import Rationals.Type using (ℚ ; 0ℚ)
 open import DedekindReals.Type fe pe pt
 open import DedekindReals.Order fe pe pt
 open import gist.RealCohesion.RationalPoints fe pe pt using (ιₐ ; ιₐ-is-ι)
 import gist.RealCohesion.FiniteChainDiscreteness fe pe pt crisp-ap-^♭ as FCD
 import gist.RealCohesion.RationalDetection fe pe pt as RD
 import gist.RealCohesion.CrispFunctionsEverywhere fe pe pt as CFE
 import gist.RealCohesion.Constancy fe pe pt as Con
 open PropositionalTruncation pt

 rational-detection
  : Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → (h : ℝ → ℝ) (x : ℝ) → 0ℚ < h x → ∃ q ꞉ ℚ , 0ℚ < h (ι q)
 rational-detection r♭ h x l =
  ∥∥-functor γ
   (RD.rational-detection (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete)
     h x l)
  where
   γ : (Σ q ꞉ ℚ , 0ℚ < h (ιₐ q)) → Σ q ꞉ ℚ , 0ℚ < h (ι q)
   γ (q , p) = q , transport (λ - → 0ℚ < h -) (ιₐ-is-ι q) p

 approximate-IVT-with-rational-witness
  : Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → (f : ℝ → ℝ) (p q a b : ℝ)
  → p < q
  → f a < q
  → p < f b
  → ∃ r ꞉ ℚ , (p < f (ι r)) × (f (ι r) < q)
 approximate-IVT-with-rational-witness r♭ =
  RD.approximate-IVT-with-rational-witness-from-constancy
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete)

 C1-and-NC-give-constancy
  : {𝓥 𝓦 : Universe} {J : 𝓥 ̇ } (R : J → 𝓦 ̇ ) → Axiom-C1 R
  → ∥ Con.Rising-Generator-Path R ∥
  → Con.Constancy
 C1-and-NC-give-constancy R c1 =
  FCD.under-C1.constancy-from-C1-and-NC R c1 𝟚-is-♭-discrete

 approximate-IVT-with-rational-witness-from-C1-and-NC
  : {𝓥 𝓦 : Universe} {J : 𝓥 ̇ } (R : J → 𝓦 ̇ ) → Axiom-C1 R
  → ∥ Con.Rising-Generator-Path R ∥
  → (f : ℝ → ℝ) (p q a b : ℝ)
  → p < q
  → f a < q
  → p < f b
  → ∃ r ꞉ ℚ , (p < f (ι r)) × (f (ι r) < q)
 approximate-IVT-with-rational-witness-from-C1-and-NC R c1 nc =
  RD.approximate-IVT-with-rational-witness-from-constancy
   (C1-and-NC-give-constancy R c1 nc)

 crisp-functions-are-continuous-everywhere-without-T
  : (@♭ cem : Crisp-EM 𝓤₁)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → (@♭ f : ℝ → ℝ) (@♭ t : ℝ) (u v : ℚ)
  → u < f t → f t < v
  → CFE.Holds-Near-Everywhere (λ s → (u < f s) × (f s < v)) t
 crisp-functions-are-continuous-everywhere-without-T cem r♭ =
  CFE.crisp-functions-are-continuous-everywhere cem
   (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete)

 exact-IVT-without-T
  : (@♭ cem : Crisp-EM 𝓤₁)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → (@♭ f : ℝ → ℝ) (@♭ c : ℝ) (a b : ℝ)
  → f a < c → c < f b
  → ∃ x ꞉ ℝ , f x ＝ c
 exact-IVT-without-T cem r♭ =
  CFE.exact-IVT cem (FCD.maps-from-ℝ-to-Q-are-constant r♭ 𝟚-is-♭-discrete)

\end{code}

Shulman's Corollary 11.6 without Axiom T. Assuming crisp excluded
middle and Axiom R♭, besides function extensionality, propositional
extensionality and propositional truncations, the canonical map
♭ (ℝ → ℝ) → (♭ ℝ → ♭ ℝ) is an embedding whose image consists of the
ε-δ continuous maps, so that ♭ (ℝ → ℝ) is equivalent to the type of
ε-δ continuous maps ♭ ℝ → ♭ ℝ (gist.RealCohesion.FlatRealFunctions,
with crisp-ap-^♭ and the ♭-discreteness of 𝟚 and of ♭ ℝ discharged).
That the canonical map is an embedding, and that crisp functions are
determined by their values at crisp points, needs only Axiom R♭.
Shulman's version also assumes Axiom T, and deduces injectivity from
the concreteness of ℝ, which is stated with ♯.

\begin{code}

module _ (@♭ fe : Fun-Ext)
         (@♭ pe : Prop-Ext)
         (@♭ pt : propositional-truncations-exist)
       where

 open import UF.Embeddings using (is-embedding)
 open import DedekindReals.Type fe pe pt using (ℝ ; 0ℝ)
 open import gist.RealCohesion.CrispUniformContinuity fe pe pt
  using (is-ε-δ-continuous)
 import gist.RealCohesion.FlatRealFunctions fe pe pt crisp-ap-^♭ as FRF

 crisp-real-functions-are-determined-by-crisp-points
  : Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → (@♭ F G : ℝ → ℝ) → ((@♭ x : ℝ) → F x ＝ G x) → F ＝ G
 crisp-real-functions-are-determined-by-crisp-points r♭ =
  FRF.crisp-functions-agreeing-at-crisp-points-are-equal
   (FRF.maps-from-ℝ-to-Q-are-constant' r♭ 𝟚-is-♭-discrete)

 canonical-map-is-an-embedding
  : Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → is-embedding (FRF.♭-action {𝓤₁} {𝓤₁} {ℝ} {ℝ})
 canonical-map-is-an-embedding r♭ = FRF.♭-action-is-embedding r♭ 𝟚-is-♭-discrete

 Shulman-Corollary-11-6-without-T
  : (@♭ cem : Crisp-EM 𝓤₁)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → is-embedding (FRF.♭-action {𝓤₁} {𝓤₁} {ℝ} {ℝ})
  × ((h : ♭ ℝ → ♭ ℝ) → fiber FRF.♭-action h ↔ is-ε-δ-continuous h)
 Shulman-Corollary-11-6-without-T cem r♭ =
  FRF.Shulman-Corollary-11-6 r♭ 𝟚-is-♭-discrete ♭-is-♭-discrete cem

 crisp-real-functions-are-the-continuous-maps
  : (@♭ cem : Crisp-EM 𝓤₁)
  → Singly-Generated-Punctual-Cohesion ℝ 0ℝ
  → ♭ (ℝ → ℝ) ≃ (Σ h ꞉ (♭ ℝ → ♭ ℝ) , is-ε-δ-continuous h)
 crisp-real-functions-are-the-continuous-maps cem r♭ =
  FRF.crisp-functions-are-the-continuous-maps r♭ 𝟚-is-♭-discrete ♭-is-♭-discrete
   cem

\end{code}
