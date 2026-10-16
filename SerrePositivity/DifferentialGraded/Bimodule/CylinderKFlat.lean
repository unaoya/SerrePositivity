module
public import SerrePositivity.DifferentialGraded.Bimodule.RightRestriction
public import SerrePositivity.DifferentialGraded.Bimodule.RelativeKFlat
public import SerrePositivity.DifferentialGraded.Module.RestrictionTensor
public import SerrePositivity.DifferentialGraded.Tensor.ModuleCylinderKFlat

/-! # 積dg圏上のcylinderをbimoduleへ移送したときの右相対K-flat性 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

lemma rightModuleBimodule_cylinder_rightRelativeKFlat
    (M : ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ)
    (hM : Bimodule.rightRelativeKFlat A B C (BimoduleCategory.underlying A B C
      ((rightModuleBimoduleEquivalence A B C).functor.obj M))) :
    Bimodule.rightRelativeKFlat A B C (BimoduleCategory.underlying A B C
      ((rightModuleBimoduleEquivalence A B C).functor.obj
        (modulePrecylinder A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ M).I)) := by
  intro c
  have hr := moduleRelativeKFlat_of_iso A B
    (rightModuleBimoduleRightRestrictionIso A B C M c).symm (hM c)
  have ht := moduleRelativeKFlat_tensor A B (dgInterval A) (complexKFlat_interval A)
    (ForgetEnrichment.to (Complex A) ((tensorRightRestriction A B C c).obj M)) hr
  exact moduleRelativeKFlat_of_iso A B
    (rightModuleBimoduleRightRestrictionIso A B C
        (modulePrecylinder A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ M).I c ≪≫
      moduleRestrictionTensorIso A B (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
        (tensorRightRestrictionInclusion A B C c) (dgInterval A) M) ht

end SerrePositivity.DifferentialGraded
