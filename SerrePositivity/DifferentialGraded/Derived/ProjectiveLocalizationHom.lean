module
public import Mathlib.CategoryTheory.HomCongr
public import SerrePositivity.DifferentialGraded.Category.LocalizationHom
public import SerrePositivity.DifferentialGraded.Derived.ProjectiveHomotopyHom
public import SerrePositivity.DifferentialGraded.Derived.HomotopyComparison

/-! # 射影的始域に対する局所化のHom計算 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleHomotopicallyProjective_coyoneda_inverts {P : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) :
    (moduleHomotopyQuasiIso A D).IsInvertedBy
      (coyoneda.obj (op ((moduleToHomotopy A D).obj P))) := by
  intro M N f hf
  obtain ⟨M⟩ := M
  obtain ⟨N⟩ := N
  obtain ⟨g, rfl⟩ := (moduleToHomotopy A D).map_surjective f
  apply (CategoryTheory.isIso_iff_bijective _).2
  exact moduleHomotopicallyProjective_homotopy_postcompose_bijective A D hP g
    ((moduleHomotopyQuasiIso_map_iff A D g).1 hf)

/-- 射影的始域のK(D)のHomを指定D(D)のHomと同定する。 -/
def moduleProjectiveLocalizationHomEquiv {P : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) (N : ModuleHomotopyCategory A D) :
    ((moduleToHomotopy A D).obj P ⟶ N) ≃
      ((moduleHomotopyToDerivedClosed A D).obj ((moduleToHomotopy A D).obj P) ⟶
        (moduleHomotopyToDerivedClosed A D).obj N) :=
  LocalizationHom.mapEquiv (moduleHomotopyQuasiIso A D)
    (moduleHomotopyToDerivedClosed A D) _
    (moduleHomotopicallyProjective_coyoneda_inverts A D hP) N

lemma moduleProjectiveLocalizationHomEquiv_apply {P : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) {N : ModuleHomotopyCategory A D}
    (f : (moduleToHomotopy A D).obj P ⟶ N) :
    moduleProjectiveLocalizationHomEquiv A D hP N f =
      (moduleHomotopyToDerivedClosed A D).map f :=
  LocalizationHom.mapEquiv_apply _ _ _ _ _ _

lemma moduleProjectiveLocalization_map_bijective {P : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) (N : ModuleHomotopyCategory A D) :
    Function.Bijective ((moduleHomotopyToDerivedClosed A D).map
      (X := (moduleToHomotopy A D).obj P) (Y := N)) :=
  LocalizationHom.map_bijective _ _ _
    (moduleHomotopicallyProjective_coyoneda_inverts A D hP) N


/-- 主局所化関手を用いた射影的始域のHom計算。 -/
def moduleProjectiveDerivedHomEquiv {P : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) (N : ModuleCategory A D) :
    ((moduleToHomotopy A D).obj P ⟶ (moduleToHomotopy A D).obj N) ≃
      ((moduleToDerived A D).obj P ⟶ (moduleToDerived A D).obj N) :=
  (moduleProjectiveLocalizationHomEquiv A D hP ((moduleToHomotopy A D).obj N)).trans
    (Iso.homCongr ((moduleToHomotopyDerivedIso A D).app P)
      ((moduleToHomotopyDerivedIso A D).app N))

lemma moduleProjectiveDerivedHomEquiv_map {P N : ModuleCategory A D}
    (hP : moduleHomotopicallyProjective A D P) (f : P ⟶ N) :
    moduleProjectiveDerivedHomEquiv A D hP N ((moduleToHomotopy A D).map f) =
      (moduleToDerived A D).map f := by
  change ((moduleToHomotopyDerivedIso A D).app P).inv ≫
    moduleProjectiveLocalizationHomEquiv A D hP _ ((moduleToHomotopy A D).map f) ≫
      ((moduleToHomotopyDerivedIso A D).app N).hom = _
  rw [moduleProjectiveLocalizationHomEquiv_apply]
  have h := (moduleToHomotopyDerivedIso A D).hom.naturality f
  change (moduleHomotopyToDerivedClosed A D).map ((moduleToHomotopy A D).map f) ≫
    ((moduleToHomotopyDerivedIso A D).app N).hom =
      ((moduleToHomotopyDerivedIso A D).app P).hom ≫ (moduleToDerived A D).map f at h
  rw [h, Iso.inv_hom_id_assoc]

end SerrePositivity.DifferentialGraded
