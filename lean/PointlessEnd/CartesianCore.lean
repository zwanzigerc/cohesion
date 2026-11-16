import PointlessEnd.SpatialCore

/-!
# A parallel prototype of the Cartesian-chart enlargement

The old constructors `pt`, `real`, and `endc` retain their original frames;
`cart n` adds the frame of opens of `Fin n → ℝ`.  The redundant copies of the
point and line at dimensions zero and one are intentional.  This prototype
checks the collar coreflection for the enlarged category without changing the
existing countermodel or claiming to formalize its higher sheaf topos.
-/

noncomputable section

open TopologicalSpace CategoryTheory

namespace PointlessEnd.CartesianCore

inductive Chart
  | pt
  | real
  | endc (e : P) (he : e ≠ ⊥)
  | cart (n : ℕ)

namespace Chart

@[reducible] def O : Chart → Type
  | pt => Prop
  | real => Opens ℝ
  | endc e _ => G e
  | cart n => Opens (Fin n → ℝ)

instance instFrame : (U : Chart) → Order.Frame (O U)
  | pt => inferInstanceAs (Order.Frame Prop)
  | real => inferInstanceAs (Order.Frame (Opens ℝ))
  | endc e _ => inferInstanceAs (Order.Frame (G e))
  | cart n => inferInstanceAs (Order.Frame (Opens (Fin n → ℝ)))

instance : SmallCategory Chart where
  Hom U V := FrameHom (O V) (O U)
  id _ := FrameHom.id _
  comp f g := FrameHom.comp f g
  id_comp f := FrameHom.id_comp f
  comp_id f := FrameHom.comp_id f
  assoc f g h := FrameHom.comp_assoc f g h

end Chart

open PointlessEnd.CartesianCore.Chart

inductive SpatialChart
  | point
  | line
  | cart (n : ℕ)

namespace SpatialChart

@[reducible] def chart : SpatialChart → Chart
  | point => pt
  | line => real
  | cart n => Chart.cart n

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

def inclusionFullyFaithful : inclusion.FullyFaithful where
  preimage f := f
  map_preimage _ := rfl
  preimage_map _ := rfl

@[reducible] def core : Chart → SpatialChart
  | pt => point
  | real => line
  | endc _ _ => line
  | Chart.cart n => cart n

/-- Identity on spatial charts, whole-collar inclusion on each endpoint. -/
def counit (U : Chart) : chart (core U) ⟶ U :=
  match U with
  | pt => 𝟙 pt
  | real => 𝟙 real
  | endc _ he => PointlessEnd.Chart.toFrameHom (SpatialCore.collarInclusion he)
  | Chart.cart n => 𝟙 (Chart.cart n)

/-- The only new lifting branch is discharged by the already checked spatial lemma. -/
def lift {S : SpatialChart} {U : Chart} (f : chart S ⟶ U) : chart S ⟶ chart (core U) :=
  match U with
  | pt => f
  | real => f
  | Chart.cart _ => f
  | endc _ he =>
    match S with
    | point => PointlessEnd.Chart.toFrameHom
        (SpatialCore.SpatialChart.lift
          (S := SpatialCore.SpatialChart.point)
          (U := PointlessEnd.Chart.endc _ he) f)
    | line => SpatialCore.spatialLift he f
    | cart _ => SpatialCore.spatialLift he f

@[simp] theorem lift_counit {S : SpatialChart} {U : Chart} (f : chart S ⟶ U) :
    lift f ≫ counit U = f := by
  cases U with
  | pt => rfl
  | real => rfl
  | cart n => rfl
  | endc e he =>
    cases S with
    | point =>
      exact SpatialCore.SpatialChart.lift_counit
        (S := SpatialCore.SpatialChart.point) (U := PointlessEnd.Chart.endc e he) f
    | line => exact SpatialCore.spatialLift_comp he f
    | cart n => exact SpatialCore.spatialLift_comp he f

theorem lift_unique {S : SpatialChart} {U : Chart} (f : chart S ⟶ U)
    (g : chart S ⟶ chart (core U)) (hg : g ≫ counit U = f) : g = lift f := by
  cases U with
  | pt => exact hg
  | real => exact hg
  | cart n => exact hg
  | endc e he =>
    cases S with
    | point =>
      exact SpatialCore.SpatialChart.lift_unique
        (S := SpatialCore.SpatialChart.point) (U := PointlessEnd.Chart.endc e he) f g hg
    | line => exact SpatialCore.spatialLift_unique he f g hg
    | cart n => exact SpatialCore.spatialLift_unique he f g hg

def homEquiv (S : SpatialChart) (U : Chart) :
    (chart S ⟶ U) ≃ (S ⟶ core U) where
  toFun := lift
  invFun g := g ≫ counit U
  left_inv := lift_counit
  right_inv g := (lift_unique (g ≫ counit U) g rfl).symm

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

/-- The enlarged category coreflects onto its full Cartesian subcategory. -/
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

#print axioms coreflection

end SpatialChart
end PointlessEnd.CartesianCore
