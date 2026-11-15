module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourcePairing
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointAugmentation

/-!
概要：元の全source-frameの要素の始域と次数を、元の全augmentationの添字へ送る。
方針：同じ全要素のパラメーターの二射影と反対積の同じ同値を合成する。
規約：元の試験対象・単体次数・augmentationを変えない。
使われ方：同じ全augmentationの逆を同じ全実射の始域へ引き戻す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
variable (A : Type u) [CommRing A]
local instance jointSourceParametersModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointSourceParametersFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩

/-- 元の全実射の始域と次数を、元の全augmentationの反対添字にする。 -/
def strictBETotJointSourceParameterIndex :
    StrictBETotJointSourceElements A ⥤ (strictBETotJointSourceFrameIndex A)ᵒᵖ :=
  strictBETotJointSourceElementsDown A ⋙
    FrameHom.sourceFrameArrowParameters (strictBETotJointSourceFrame A)
      (rightFrameReplacement (rightFrameFamily A)) ⋙
    ((CategoryTheory.Prod.fst ((operad A).Algebraᵒᵖ × (operad A).Algebra) SimplexCategoryᵒᵖ ⋙
        CategoryTheory.Prod.fst (operad A).Algebraᵒᵖ (operad A).Algebra).prod'
      (CategoryTheory.Prod.snd ((operad A).Algebraᵒᵖ × (operad A).Algebra) SimplexCategoryᵒᵖ)) ⋙
    (prodOpEquiv (operad A).Algebra (D := SimplexCategory)).inverse ⋙
    (AsSmall.up : (operad A).Algebra × SimplexCategory ⥤ strictBETotJointSourceFrameIndex A).op

/-- 同じ全augmentationの評価の引き戻しは、元の実射の始域そのもの。 -/
theorem strictBETotJointSourceParameterIndex_evaluation :
    strictBETotJointSourceParameterIndex A ⋙ (strictBETotJointSourceFrameEvaluation A).op =
      FrameHom.liftedSourceFrameArrowDomain (strictBETotJointSourceFrame A)
        (rightFrameReplacement (rightFrameFamily A)) := rfl

/-- 同じ全augmentationの定値端の引き戻しは、元の試験対象の射影。 -/
theorem strictBETotJointSourceParameterIndex_constant :
    strictBETotJointSourceParameterIndex A ⋙ (strictBETotJointSourceFrameConstant A).op =
      strictBETotJointSourceElementsProjection A ⋙ strictBETotJointHomSourceIndex A := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply Quiver.Hom.unop_inj
  apply ULift.ext
  change ((f.hom.1.down.1).unop ≫ 𝟙 _) = (f.hom.1.down.1).unop
  exact Category.comp_id _
end SerrePositivity.EInfinity.BarrattEccles
