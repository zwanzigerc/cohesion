Claude Opus 5.5, an AI model made by Anthropic, prompted by Colin
Zwanziger, 25 October 2026; prose updated 27 October 2026. See the AI
disclosure in
gist.RealCohesion.index.

The frame-level forms of the binary-bar conditions.

The conditions B1–B4 of gist.RealCohesion.AnalyticMarkovObstruction
are internal statements. In the pointless-end countermodel they come
from identities between opens of the glued frame Gl of
gist.RealCohesion.PointlessEnd, for its bar bar s = (𝟏 , cyl′ s),
where cyl′ s is the complement of the cylinder of s:

 B1: bar [] is the collar,
 B2: bar s = bar (s ⌢ ₀) ∧ bar (s ⌢ ₁),
 B3: bar (s ⌢ ₀) ∨ bar (s ⌢ ₁) = 𝟏,
 B4: for every sequence α, the opens bar (α ↾ n) cover.

B4 is gist.RealCohesion.PointlessEnd.glued-frame.fan.bar-is-a-bar. We
prove B1–B3 here, from the corresponding identities for the
complements of the cylinders. Like the results of
gist.RealCohesion.PointlessEnd, these are statements about frames,
relative to the hypotheses on the frames involved. Their transfer to
internal statements about sheaves is not formalized in Agda; it is
formalized in Lean, as gist.RealCohesion.AnalyticMarkovObstruction
explains.

\begin{code}

{-# OPTIONS --safe --without-K #-}

open import MLTT.Spartan
open import MLTT.List hiding ([_])
open import UF.FunExt
open import UF.PropTrunc
open import UF.Subsingletons

module gist.RealCohesion.BinaryBarFrame
        (pt : propositional-truncations-exist)
        (fe : Fun-Ext)
        (pe : Prop-Ext)
       where

open import Locales.Frame pt fe hiding (𝟚 ; ₀ ; ₁)
open import UF.Base
open import UF.SubtypeClassifier
open import gist.RealCohesion.Cylinders pt fe
open import gist.RealCohesion.PointlessEnd pt fe pe

\end{code}

The complements of the cylinders.

\begin{code}

module _ {B : Frame 𝓤 𝓥 𝓦} (𝒞 : Cylinder-System B) where

 open Cylinder-System 𝒞
 open PosetNotation (poset-of B)
 open PosetReasoning (poset-of B)

 disjoint-gives-below-complement : (s : List 𝟚) (x : ⟨ B ⟩)
                                 → x ∧[ B ] cyl s ＝ 𝟎[ B ]
                                 → (x ≤ cyl′ s) holds
 disjoint-gives-below-complement s x p =
  complements-are-antitone 𝒞 (cyl s) (cyl s) (cyl′ s) x
   (≤-is-reflexive (poset-of B) (cyl s))
   (pr₂ (cyl′-is-complement s))
   (∧[ B ]-is-commutative (cyl s) x ∙ p)

 complement-of-the-empty-word : cyl′ [] ＝ 𝟎[ B ]
 complement-of-the-empty-word =
  cyl′ []               ＝⟨ 𝟏-right-unit-of-∧ B (cyl′ []) ⁻¹ ⟩
  cyl′ [] ∧[ B ] 𝟏[ B ] ＝⟨ ap (λ - → cyl′ [] ∧[ B ] -) (cyl-root ⁻¹) ⟩
  cyl′ [] ∧[ B ] cyl [] ＝⟨ ∧[ B ]-is-commutative (cyl′ []) (cyl []) ⟩
  cyl [] ∧[ B ] cyl′ [] ＝⟨ pr₁ (cyl′-is-complement []) ⟩
  𝟎[ B ]                ∎

 complements-of-children-meet : (s : List 𝟚)
                              → cyl′ (s ⌢ ₀) ∧[ B ] cyl′ (s ⌢ ₁) ＝ cyl′ s
 complements-of-children-meet s = ≤-is-antisymmetric (poset-of B) I II
  where
   x : ⟨ B ⟩
   x = cyl′ (s ⌢ ₀) ∧[ B ] cyl′ (s ⌢ ₁)

   x-misses-the-cylinder : x ∧[ B ] cyl s ＝ 𝟎[ B ]
   x-misses-the-cylinder =
    disjoint-from-both-children 𝒞 s x
     (below-complement-gives-disjoint 𝒞 (s ⌢ ₀) x
       (∧[ B ]-lower₁ (cyl′ (s ⌢ ₀)) (cyl′ (s ⌢ ₁))))
     (below-complement-gives-disjoint 𝒞 (s ⌢ ₁) x
       (∧[ B ]-lower₂ (cyl′ (s ⌢ ₀)) (cyl′ (s ⌢ ₁))))

   I : (x ≤ cyl′ s) holds
   I = disjoint-gives-below-complement s x x-misses-the-cylinder

   II : (cyl′ s ≤ x) holds
   II = ∧[ B ]-greatest (cyl′ (s ⌢ ₀)) (cyl′ (s ⌢ ₁)) (cyl′ s)
         (complements-grow 𝒞 ₀ s)
         (complements-grow 𝒞 ₁ s)

 complements-of-children-cover : (s : List 𝟚)
                               → cyl′ (s ⌢ ₀) ∨[ B ] cyl′ (s ⌢ ₁) ＝ 𝟏[ B ]
 complements-of-children-cover s = only-𝟏-is-above-𝟏 B _ γ
  where
   δ : (cyl (s ⌢ ₀) ≤ cyl′ (s ⌢ ₁)) holds
   δ = disjoint-gives-below-complement (s ⌢ ₁) (cyl (s ⌢ ₀)) (cyl-disjoint s)

   ε : (cyl (s ⌢ ₀) ≤ (cyl′ (s ⌢ ₀) ∨[ B ] cyl′ (s ⌢ ₁))) holds
   ε = cyl (s ⌢ ₀)                      ≤⟨ δ ⟩
       cyl′ (s ⌢ ₁)
        ≤⟨ ∨[ B ]-upper₂ (cyl′ (s ⌢ ₀)) (cyl′ (s ⌢ ₁)) ⟩
       cyl′ (s ⌢ ₀) ∨[ B ] cyl′ (s ⌢ ₁) ■

   γ : (𝟏[ B ] ≤ (cyl′ (s ⌢ ₀) ∨[ B ] cyl′ (s ⌢ ₁))) holds
   γ =
    𝟏[ B ]                           ＝⟨ pr₂ (cyl′-is-complement (s ⌢ ₀)) ⁻¹ ⟩ₚ
       cyl (s ⌢ ₀) ∨[ B ] cyl′ (s ⌢ ₀)  ≤⟨ ∨[ B ]-least ε
                                            (∨[ B ]-upper₁ (cyl′ (s ⌢ ₀))
                                                           (cyl′ (s ⌢ ₁))) ⟩
       cyl′ (s ⌢ ₀) ∨[ B ] cyl′ (s ⌢ ₁) ■

\end{code}

The bar of the glued frame. Meets and joins in Gl are computed
componentwise, and the open parts of the bar are all 𝟏.

\begin{code}

module _ {𝓤 𝓥 𝓤' 𝓥' 𝓦 : Universe}
         (O : Frame 𝓤 𝓥 𝓦)
         (B : Frame 𝓤' 𝓥' 𝓦)
         (C : ⟨ O ⟩ → Ω 𝓦)
         (C-is-upward-closed : (V W : ⟨ O ⟩)
                             → (V ≤[ poset-of O ] W) holds
                             → C V holds → C W holds)
         (C-contains-𝟏 : C 𝟏[ O ] holds)
         (C-is-closed-under-∧ : (V W : ⟨ O ⟩)
                              → C V holds → C W holds → C (V ∧[ O ] W) holds)
         (𝒞 : Cylinder-System B)
       where

 open glued-frame O B C C-is-upward-closed C-contains-𝟏 C-is-closed-under-∧
 open fan 𝒞

 bar-at-the-empty-word-is-the-collar : bar [] ＝ collar
 bar-at-the-empty-word-is-the-collar =
  to-Glued-＝ refl (complement-of-the-empty-word 𝒞)

 bar-splits : (s : List 𝟚) → bar s ＝ bar (s ⌢ ₀) ∧[ Gl ] bar (s ⌢ ₁)
 bar-splits s = to-Glued-＝ (𝟏-right-unit-of-∧ O 𝟏[ O ] ⁻¹)
                           (complements-of-children-meet 𝒞 s ⁻¹)

 bar-has-the-sibling-cover : (s : List 𝟚)
                           → bar (s ⌢ ₀) ∨[ Gl ] bar (s ⌢ ₁) ＝ 𝟏[ Gl ]
 bar-has-the-sibling-cover s =
  to-Glued-＝ (open-part-of-∨ (bar (s ⌢ ₀)) (bar (s ⌢ ₁))
               ∙ 𝟏-right-annihilator-for-∨ O 𝟏[ O ])
              (closed-part-of-∨ (bar (s ⌢ ₀)) (bar (s ⌢ ₁))
               ∙ complements-of-children-cover 𝒞 s)

\end{code}
