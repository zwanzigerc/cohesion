import Cohesion.Pullbacks
import Cohesion.Precohesive
import Mathlib.CategoryTheory.Extensive
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# The categorical argument behind the Boolean-base theorem

A functor between extensive categories which preserves binary coproducts
preserves pullbacks of complemented inclusions. Together with preservation
of binary products this implies preservation of pullbacks over objects
whose diagonal is complemented.

The assumptions are stated explicitly. Deriving extensivity from the
elementary-topos axioms is a separate foundational obligation.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Positive

universe v₁ v₂ u₁ u₂
variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- A morphism is complemented when it is one leg of an actual binary coproduct. -/
def IsComplementedInclusion {A B : C} (m : A ⟶ B) : Prop :=
  ∃ (N : C) (n : N ⟶ B), Nonempty (IsColimit (BinaryCofan.mk m n))

theorem map_pullback_of_coproduct
    [HasPullbacks C] [FinitaryExtensive C] [FinitaryExtensive D]
    (F : C ⥤ D) [PreservesColimitsOfShape (Discrete WalkingPair) F]
    {A N B P X : C} (m : A ⟶ B) (n : N ⟶ B)
    (hc : IsColimit (BinaryCofan.mk m n))
    (p : P ⟶ X) (q : P ⟶ A) (f : X ⟶ B)
    (sq : IsPullback p q f m) :
    IsPullback (F.map p) (F.map q) (F.map f) (F.map m) := by
  let r : pullback n f ⟶ X := pullback.snd n f
  let s : pullback n f ⟶ N := pullback.fst n f
  have hs : s ≫ n = r ≫ f := pullback.condition
  have hc' : IsColimit (BinaryCofan.mk p r) :=
    (((BinaryCofan.isVanKampen_iff _).mp
      (FinitaryExtensive.vanKampen _ hc)) (BinaryCofan.mk p r) q s f
        sq.w.symm hs).mpr ⟨sq, (IsPullback.of_hasPullback n f).flip⟩ |>.some
  have hmap := (BinaryCofan.isVanKampen_iff _).mp
    (FinitaryExtensive.vanKampen _ (mapIsColimitOfPreservesOfIsColimit F m n hc))
      (BinaryCofan.mk (F.map p) (F.map r)) (F.map q) (F.map s) (F.map f)
      (by simpa only [BinaryCofan.mk_inl, ← F.map_comp] using congrArg F.map sq.w.symm)
      (by simpa only [BinaryCofan.mk_inr, ← F.map_comp] using congrArg F.map hs)
  exact (hmap.mp ⟨mapIsColimitOfPreservesOfIsColimit F p r hc'⟩).1

theorem map_pullback_of_complemented
    [HasPullbacks C] [FinitaryExtensive C] [FinitaryExtensive D]
    (F : C ⥤ D) [PreservesColimitsOfShape (Discrete WalkingPair) F]
    {A B P X : C} {m : A ⟶ B} (hm : IsComplementedInclusion m)
    (p : P ⟶ X) (q : P ⟶ A) (f : X ⟶ B)
    (sq : IsPullback p q f m) :
    IsPullback (F.map p) (F.map q) (F.map f) (F.map m) := by
  obtain ⟨N, n, ⟨hc⟩⟩ := hm
  exact map_pullback_of_coproduct F m n hc p q f sq

section Diagonal
variable [HasBinaryProducts C]

/-- A pullback is the inverse image of the diagonal under the product of its two maps. -/
theorem pullback_diagonal {P X Y Z : C} {p : P ⟶ X} {q : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (sq : IsPullback p q f g) :
    IsPullback (prod.lift p q) (p ≫ f) (prod.map f g) (prod.lift (𝟙 Z) (𝟙 Z)) := by
  have w : prod.lift p q ≫ prod.map f g = (p ≫ f) ≫ prod.lift (𝟙 Z) (𝟙 Z) := by
    ext <;> simp [sq.w]
  apply IsPullback.of_isLimit (c := PullbackCone.mk _ _ w)
  refine PullbackCone.IsLimit.mk w (fun s => sq.lift (s.fst ≫ prod.fst)
    (s.fst ≫ prod.snd) ?_) ?_ ?_ ?_
  · have h₁ := congrArg (fun k => k ≫ prod.fst) s.condition
    have h₂ := congrArg (fun k => k ≫ prod.snd) s.condition
    simp only [Category.assoc, prod.map_fst, prod.map_snd, prod.lift_fst, prod.lift_snd,
      Category.comp_id] at h₁ h₂
    simpa only [Category.assoc] using h₁.trans h₂.symm
  · intro s
    ext <;> simp
  · intro s
    have h₁ := congrArg (fun k => k ≫ prod.fst) s.condition
    simpa using h₁
  · intro s m h₁ h₂
    apply sq.hom_ext
    · simpa using congrArg (fun k => k ≫ prod.fst) h₁
    · simpa using congrArg (fun k => k ≫ prod.snd) h₁

theorem pullback_of_diagonal {P X Y Z : C} {p : P ⟶ X} {q : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (w : p ≫ f = q ≫ g)
    (sq : IsPullback (prod.lift p q) (p ≫ f) (prod.map f g)
      (prod.lift (𝟙 Z) (𝟙 Z))) : IsPullback p q f g := by
  apply IsPullback.of_isLimit (c := PullbackCone.mk p q w)
  refine PullbackCone.IsLimit.mk w (fun s => sq.lift (prod.lift s.fst s.snd)
    (s.fst ≫ f) ?_) ?_ ?_ ?_
  · ext <;> simp [s.condition]
  · intro s
    simpa using congrArg (fun k => k ≫ prod.fst)
      (sq.lift_fst (prod.lift s.fst s.snd) (s.fst ≫ f) _)
  · intro s
    simpa using congrArg (fun k => k ≫ prod.snd)
      (sq.lift_fst (prod.lift s.fst s.snd) (s.fst ≫ f) _)
  · intro s m h₁ h₂
    apply sq.hom_ext
    · rw [sq.lift_fst]
      ext <;> simp [h₁, h₂]
    · rw [sq.lift_snd]
      simp [← Category.assoc, h₁]

end Diagonal

/-- Product and coproduct preservation suffice for pullbacks over a decidable object. -/
theorem map_pullback_of_complemented_diagonal
    [HasPullbacks C] [HasBinaryProducts C] [HasBinaryProducts D]
    [FinitaryExtensive C] [FinitaryExtensive D]
    (F : C ⥤ D) [PreservesColimitsOfShape (Discrete WalkingPair) F]
    [PreservesLimitsOfShape (Discrete WalkingPair) F]
    {P X Y Z : C} (p : P ⟶ X) (q : P ⟶ Y) (f : X ⟶ Z) (g : Y ⟶ Z)
    (hZ : IsComplementedInclusion (prod.lift (𝟙 Z) (𝟙 Z)))
    (sq : IsPullback p q f g) :
    IsPullback (F.map p) (F.map q) (F.map f) (F.map g) := by
  have hs := map_pullback_of_complemented F hZ (prod.lift p q) (p ≫ f)
    (prod.map f g) (pullback_diagonal sq)
  apply pullback_of_diagonal
    (by simpa only [← F.map_comp] using congrArg F.map sq.w)
  apply hs.of_iso (Iso.refl _) (asIso (prodComparison F X Y)) (Iso.refl _)
    (asIso (prodComparison F Z Z))
  · ext <;> simp [← F.map_comp]
  · simp
  · simpa using (prodComparison_natural F f g)
  · ext <;> simp [← F.map_comp]

theorem IsComplementedInclusion.map
    (F : C ⥤ D) [PreservesColimitsOfShape (Discrete WalkingPair) F]
    {A B : C} {m : A ⟶ B} (hm : IsComplementedInclusion m) :
    IsComplementedInclusion (F.map m) := by
  obtain ⟨N, n, ⟨hc⟩⟩ := hm
  exact ⟨F.obj N, F.map n, ⟨mapIsColimitOfPreservesOfIsColimit F m n hc⟩⟩

theorem IsComplementedInclusion.comp_iso
    {A B B' : C} {m : A ⟶ B} (hm : IsComplementedInclusion m) (e : B ≅ B') :
    IsComplementedInclusion (m ≫ e.hom) := by
  obtain ⟨N, n, ⟨hc⟩⟩ := hm
  refine ⟨N, n ≫ e.hom, ⟨hc.ofIsoColimit ?_⟩⟩
  exact Cocone.ext e (by rintro ⟨⟨⟩⟩ <;> simp)

theorem complemented_diagonal_map
    [HasBinaryProducts C] [HasBinaryProducts D]
    (F : C ⥤ D) [PreservesColimitsOfShape (Discrete WalkingPair) F]
    [PreservesLimitsOfShape (Discrete WalkingPair) F]
    (B : C) (hB : IsComplementedInclusion (prod.lift (𝟙 B) (𝟙 B))) :
    IsComplementedInclusion (prod.lift (𝟙 (F.obj B)) (𝟙 (F.obj B))) := by
  have h := (hB.map F).comp_iso (asIso (prodComparison F B B))
  have heq : F.map (prod.lift (𝟙 B) (𝟙 B)) ≫ prodComparison F B B =
      prod.lift (𝟙 (F.obj B)) (𝟙 (F.obj B)) := by
    ext <;> simp [← F.map_comp]
  simpa only [asIso_hom, heq] using h

/-- The Boolean-base argument with all ambient categorical hypotheses explicit. -/
theorem locallyConnected_of_complementedMonomorphisms
    [HasFiniteLimits C] [HasFiniteLimits D] [FinitaryExtensive C] [FinitaryExtensive D]
    (p : Cohesion.PrecohesiveMorphism C D)
    (hBoolean : ∀ {A B : D} (m : A ⟶ B) [Mono m], IsComplementedInclusion m) :
    p.LocallyConnected := by
  let : PreservesFiniteProducts p.pieces := p.piecesPreservesFiniteProducts
  let : PreservesFiniteLimits p.discrete := p.discretePreservesFiniteLimits
  let : PreservesColimitsOfSize.{0, 0} p.pieces :=
    p.adjunctions.adj₁.leftAdjoint_preservesColimits
  let : PreservesColimitsOfSize.{0, 0} p.discrete :=
    p.adjunctions.adj₂.leftAdjoint_preservesColimits
  intro A B f P X r s g sq
  exact map_pullback_of_complemented_diagonal p.pieces r s g (p.discrete.map f)
    (complemented_diagonal_map p.discrete B (hBoolean (prod.lift (𝟙 B) (𝟙 B)))) sq

end Positive
