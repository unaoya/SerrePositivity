module
public import SerrePositivity.DifferentialGraded.Tensor.RestrictionSemifree
public import SerrePositivity.DifferentialGraded.Bimodule.RightRestriction
public import SerrePositivity.DifferentialGraded.Bimodule.SemifreeResolution
public import SerrePositivity.DifferentialGraded.Bimodule.RelativeKFlat

/-! # 生成cellの右制限からbimodule解像度の右相対K-flat性への帰着 -/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

/-- ここでは生成cellの制限の条件を明示して残す。local Hom条件からの証明は別工程。 -/
lemma rightModuleBimodule_semifree_rightRelativeKFlat
    (hcell : ∀ (c : C) (x : (DGTensorCategory A Bᵒᵖ C)ᵒᵖ) (n : ℤ),
      moduleRelativeKFlat A B (ForgetEnrichment.to (Complex A)
        ((tensorRightRestriction A B C c).obj (freeSphere A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ x n))))
    {M : ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ}
    (hM : moduleSemifree A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ M) :
    Bimodule.rightRelativeKFlat A B C (BimoduleCategory.underlying A B C
      ((rightModuleBimoduleEquivalence A B C).functor.obj M)) := by
  intro c
  exact moduleRelativeKFlat_of_iso A B (rightModuleBimoduleRightRestrictionIso A B C M c)
    (moduleSemifree_restriction_relativeKFlat A B (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
      (tensorRightRestrictionInclusion A B C c) (hcell c) hM)

lemma BimoduleSemifreeResolution.rightRelativeKFlat_of_cells
    {M : BimoduleCategory A B C} (P : BimoduleSemifreeResolution A B C M)
    (hcell : ∀ (c : C) (x : (DGTensorCategory A Bᵒᵖ C)ᵒᵖ) (n : ℤ),
      moduleRelativeKFlat A B (ForgetEnrichment.to (Complex A)
        ((tensorRightRestriction A B C c).obj (freeSphere A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ x n)))) :
    Bimodule.rightRelativeKFlat A B C (BimoduleCategory.underlying A B C P.obj) :=
  rightModuleBimodule_semifree_rightRelativeKFlat A B C hcell P.semifree

end SerrePositivity.DifferentialGraded
