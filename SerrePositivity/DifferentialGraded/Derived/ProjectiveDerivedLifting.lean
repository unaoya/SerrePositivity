module
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveLocalizationHom

/-! # 射影的始域の導来射を実際の加群射へ持ち上げる -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleProjectiveToDerived_map_surjective {P N : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) :
    Function.Surjective ((moduleToDerived A D).map (X := P) (Y := N)) := by
  intro f
  obtain ⟨g, hg⟩ := (moduleToHomotopy A D).map_surjective
    ((moduleProjectiveDerivedHomEquiv A D hP N).symm f)
  refine ⟨g, ?_⟩
  rw [← moduleProjectiveDerivedHomEquiv_map A D hP, hg, Equiv.apply_symm_apply]

end SerrePositivity.DifferentialGraded
