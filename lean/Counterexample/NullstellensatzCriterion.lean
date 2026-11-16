import Counterexample.PresheafReflection

/-!
# The split-unit criterion for the presheaf Nullstellensatz

This adds the converse to the sufficient criterion in `PresheafReflection`.
The proof uses the universal property of the actual left Kan extension
and Yoneda, and imposes no finite-completeness assumption.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor
  CategoryTheory.ConcreteCategory Opposite

universe u

namespace Precohesion.PresheafReflection

variable {A B : Type u} [SmallCategory A] [SmallCategory B]
variable {a : B ⥤ A} {i : A ⥤ B} (adj : a ⊣ i) [i.Full] [i.Faithful]

/-- Epicness of the points-to-pieces comparison on all presheaves forces
each unit of the original reflection to have a section. -/
theorem split_units_of_theta_epi (hθ : ∀ X, Epi ((theta adj).app X)) (G : B) :
    IsSplitEpi (adj.unit.app G) := by
  let : (discrete a).Full := (discreteFullyFaithful adj).full
  let : (discrete a).Faithful := (discreteFullyFaithful adj).faithful
  let F := yoneda.obj G
  let K := a.op.lan.obj F
  let η := a.op.lanUnit.app F
  let ν : K ⟶ yoneda.obj (a.obj G) :=
    K.descOfIsLeftKanExtension η _ (yonedaMap a G)
  have hfac (T : B) (k : T ⟶ G) :
      ν.app (op (a.obj T)) (η.app (op T) k) = a.map k := by
    exact congr_hom (K.descOfIsLeftKanExtension_fac_app η _ (yonedaMap a G) (op T)) k
  have hep : Epi ((points i).map ((quadruple adj).adj₁.unit.app F)) :=
    ((quadruple adj).leftTriple.epi_rightToLeft_app_iff_epi_map_adj₁_unit_app).1 (hθ F)
  have hepc := (NatTrans.epi_iff_epi_app _).1 hep (op (a.obj G))
  have hsurj : Function.Surjective (η.app (op (i.obj (a.obj G)))) := by
    exact (CategoryTheory.epi_iff_surjective _).1 hepc
  let z := K.map (adj.counit.app (a.obj G)).op (η.app (op G) (𝟙 G))
  obtain ⟨h, hh⟩ := hsurj z
  have hn := congr_hom (ν.naturality (adj.counit.app (a.obj G)).op)
    (η.app (op G) (𝟙 G))
  change ν.app (op (a.obj (i.obj (a.obj G)))) z =
    adj.counit.app (a.obj G) ≫ ν.app (op (a.obj G)) (η.app (op G) (𝟙 G)) at hn
  simp only [hfac, a.map_id] at hn
  have hm : a.map h = adj.counit.app (a.obj G) := by
    rw [← hfac (i.obj (a.obj G)) h, hh]
    exact hn.trans (Category.comp_id _)
  refine ⟨⟨{ section_ := h, id := ?_ }⟩⟩
  have ht := congrArg (adj.homEquiv (i.obj (a.obj G)) (a.obj G)) hm
  calc
    h ≫ adj.unit.app G = adj.unit.app (i.obj (a.obj G)) ≫ i.map (a.map h) :=
      adj.unit.naturality h
    _ = 𝟙 _ := by
      change adj.unit.app (i.obj (a.obj G)) ≫ i.map (a.map h) = 𝟙 (i.obj (a.obj G))
      simpa only [Adjunction.homEquiv_apply, adj.right_triangle_components] using ht

/-- Menni's criterion for the trivial topology: the canonical comparison
is epic on every presheaf exactly when every reflection unit splits. -/
theorem theta_epi_iff_split_units :
    (∀ X, Epi ((theta adj).app X)) ↔ ∀ G, IsSplitEpi (adj.unit.app G) := by
  constructor
  · exact split_units_of_theta_epi adj
  · intro h
    let : ∀ G, IsSplitEpi (adj.unit.app G) := h
    exact theta_epi_of_split_units adj

end Precohesion.PresheafReflection
