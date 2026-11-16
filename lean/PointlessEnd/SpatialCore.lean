import PointlessEnd.Charts
import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# Spatial maps factor uniquely through the collar

This supplement imports the unchanged, checked minimal-site development.  It proves the
collar factorization for maps from the locale of opens of **any topological space**, so in
particular for every Cartesian space.  It then constructs the spatial coreflection of the
old category of charts onto its full subcategory on `pt` and `real`.

No statement about infinity-categorical siftedness is encoded here.
-/

noncomputable section

open Set TopologicalSpace CategoryTheory

namespace PointlessEnd.SpatialCore

open Chart

/-- Evaluation at an ordinary point is a locale point. -/
def evalPoint {X : Type*} [TopologicalSpace X] (x : X) : FrameHom (Opens X) Prop where
  toFun V := x ∈ V
  map_inf' _ _ := rfl
  map_top' := rfl
  map_sSup' S := by simp [Prop.exists_iff]

/-- Every locale map from a spatial locale to an endpoint locale lands in the collar. -/
theorem map_collar_top {X : Type*} [TopologicalSpace X] {e : P}
    (f : FrameHom (G e) (Opens X)) : f (collar e) = ⊤ := by
  apply Opens.ext
  apply Set.eq_univ_of_forall
  intro x
  obtain ⟨t, ht, hp⟩ := point_eq_collarPt ((evalPoint x).comp f)
  have h := congrArg (fun p : FrameHom (G e) Prop => p (collar e)) hp
  change (x ∈ f (collar e)) = (t ∈ (collar e).V) at h
  change x ∈ f (collar e)
  rw [h]
  exact ht

/-- The chosen chart presentation of the entire collar, isomorphic to the real line. -/
def collarInclusion {e : P} (he : e ≠ ⊥) : real ⟶ endc e he :=
  collarEmb he 0 1 (by norm_num) le_rfl le_rfl

theorem collarIvl_eq (e : P) : collarIvl e 0 1 le_rfl le_rfl = collar e := by
  apply G.ext <;> rfl

theorem collarInclusion_open {e : P} (he : e ≠ ⊥) :
    IsOpenEmb (collarInclusion he) (collar e) := by
  simpa only [collarInclusion, collarIvl_eq] using
    (isOpenEmb_collarEmb he (a := 0) (b := 1) (by norm_num) le_rfl le_rfl)

/-- The unique lift of a spatial locale map through the collar. -/
def spatialLift {X : Type*} [TopologicalSpace X] {e : P} (he : e ≠ ⊥)
    (f : FrameHom (G e) (Opens X)) : FrameHom (Opens ℝ) (Opens X) where
  toFun V := f ((collarInclusion_open he).inv V)
  map_inf' V W := by rw [IsOpenEmb.inv_inf, map_inf]
  map_top' := by rw [IsOpenEmb.inv_top, map_collar_top]
  map_sSup' S := by rw [IsOpenEmb.inv_sSup, map_iSup₂, sSup_image]

@[simp] theorem spatialLift_comp {X : Type*} [TopologicalSpace X] {e : P}
    (he : e ≠ ⊥) (f : FrameHom (G e) (Opens X)) :
    (spatialLift he f).comp (toFrameHom (collarInclusion he)) = f := by
  apply FrameHom.ext
  intro V
  change f ((collarInclusion_open he).inv (collarInclusion he V)) = f V
  rw [IsOpenEmb.inv_map, map_inf, map_collar_top, inf_top_eq]

theorem spatialLift_unique {X : Type*} [TopologicalSpace X] {e : P}
    (he : e ≠ ⊥) (f : FrameHom (G e) (Opens X))
    (g : FrameHom (Opens ℝ) (Opens X))
    (hg : g.comp (toFrameHom (collarInclusion he)) = f) : g = spatialLift he f := by
  apply FrameHom.ext
  intro V
  have h := congrArg (fun k : FrameHom (G e) (Opens X) =>
    k ((collarInclusion_open he).inv V)) hg
  change g (collarInclusion he ((collarInclusion_open he).inv V)) =
    f ((collarInclusion_open he).inv V) at h
  rw [IsOpenEmb.map_inv] at h
  exact h

/-- The universal property, for every spatial source; this includes every `ℝⁿ`. -/
theorem existsUnique_spatialLift {X : Type*} [TopologicalSpace X] {e : P}
    (he : e ≠ ⊥) (f : FrameHom (G e) (Opens X)) :
    ∃! g : FrameHom (Opens ℝ) (Opens X),
      g.comp (toFrameHom (collarInclusion he)) = f :=
  ⟨spatialLift he f, spatialLift_comp he f, fun g hg => spatialLift_unique he f g hg⟩

/-- Explicit specialization to the Cartesian charts used in the repaired higher site. -/
theorem existsUnique_cartesianLift (n : ℕ) {e : P} (he : e ≠ ⊥)
    (f : FrameHom (G e) (Opens (Fin n → ℝ))) :
    ∃! g : FrameHom (Opens ℝ) (Opens (Fin n → ℝ)),
      g.comp (toFrameHom (collarInclusion he)) = f :=
  existsUnique_spatialLift he f

/-- The spatial objects of the unchanged minimal chart category. -/
inductive SpatialChart
  | point
  | line

namespace SpatialChart

@[reducible] def chart : SpatialChart → Chart
  | point => pt
  | line => real

instance : SmallCategory SpatialChart where
  Hom S T := chart S ⟶ chart T
  id S := 𝟙 (chart S)
  comp f g := f ≫ g
  id_comp := Category.id_comp
  comp_id := Category.comp_id
  assoc := Category.assoc

@[reducible] def inclusion : SpatialChart ⥤ Chart where
  obj := chart
  map f := f

/-- The spatial charts form a full subcategory. -/
def inclusionFullyFaithful : inclusion.FullyFaithful where
  preimage f := f
  map_preimage _ := rfl
  preimage_map _ := rfl

/-- The collar core of an old chart. -/
@[reducible] def core : Chart → SpatialChart
  | pt => point
  | real => line
  | endc _ _ => line

/-- The core counit: identity for spatial charts, collar inclusion for endpoints. -/
def counit (U : Chart) : chart (core U) ⟶ U :=
  match U with
  | pt => 𝟙 pt
  | real => 𝟙 real
  | endc _ he => collarInclusion he

theorem spatial_collar_top (S : SpatialChart) {e : P} (he : e ≠ ⊥)
    (f : chart S ⟶ endc e he) : f (collar e) = ⊤ := by
  cases S with
  | point =>
    obtain ⟨t, ht, rfl⟩ := end_point f
    exact propext (iff_true_intro ht)
  | line => exact map_collar_top (toFrameHom f)

/-- Universal factorization from a spatial chart through the core counit. -/
def lift {S : SpatialChart} {U : Chart} (f : chart S ⟶ U) : chart S ⟶ chart (core U) :=
  match U with
  | pt => f
  | real => f
  | endc _ he => (collarInclusion_open he).lift f (spatial_collar_top S he f)

@[simp] theorem lift_counit {S : SpatialChart} {U : Chart} (f : chart S ⟶ U) :
    lift f ≫ counit U = f := by
  cases U with
  | pt => exact Category.comp_id f
  | real => exact Category.comp_id f
  | endc e he => exact (collarInclusion_open he).lift_comp f (spatial_collar_top S he f)

theorem lift_unique {S : SpatialChart} {U : Chart} (f : chart S ⟶ U)
    (g : chart S ⟶ chart (core U)) (hg : g ≫ counit U = f) : g = lift f := by
  cases U with
  | pt => simpa only [counit, lift, core, chart, Category.comp_id] using hg
  | real => simpa only [counit, lift, core, chart, Category.comp_id] using hg
  | endc e he => exact (collarInclusion_open he).eq_lift (spatial_collar_top S he f) hg

/-- The universal collar equivalence, on the original site. -/
def homEquiv (S : SpatialChart) (U : Chart) :
    (chart S ⟶ U) ≃ (S ⟶ core U) where
  toFun := lift
  invFun g := g ≫ counit U
  left_inv := lift_counit
  right_inv g := (lift_unique (g ≫ counit U) g rfl).symm

/-- Functoriality of taking the spatial core follows from its universal property. -/
def coreFunctor : Chart ⥤ SpatialChart where
  obj := core
  map {U V} f := lift (counit U ≫ f)
  map_id U := by
    apply (lift_unique (counit U ≫ 𝟙 U) (𝟙 (chart (core U))) _).symm
    simp
  map_comp {U V W} f g := by
    apply (lift_unique (counit U ≫ (f ≫ g))
      (lift (counit U ≫ f) ≫ lift (counit V ≫ g)) _).symm
    rw [Category.assoc, lift_counit, ← Category.assoc, lift_counit, Category.assoc]

/-- The inclusion of the old spatial charts is left adjoint to the collar core. -/
def coreflection : inclusion ⊣ coreFunctor := Adjunction.mkOfHomEquiv {
  homEquiv := homEquiv
  homEquiv_naturality_left_symm := by
    intro S T U f g
    exact @Category.assoc Chart _ _ _ _ _ f g (counit U)
  homEquiv_naturality_right := by
    intro S U V f g
    change lift (f ≫ g) = lift f ≫ lift (counit U ≫ g)
    apply (lift_unique (f ≫ g) _ _).symm
    rw [Category.assoc, lift_counit, ← Category.assoc, lift_counit]
}

end SpatialChart

#print axioms map_collar_top
#print axioms existsUnique_spatialLift
#print axioms existsUnique_cartesianLift
#print axioms SpatialChart.coreflection

end PointlessEnd.SpatialCore
