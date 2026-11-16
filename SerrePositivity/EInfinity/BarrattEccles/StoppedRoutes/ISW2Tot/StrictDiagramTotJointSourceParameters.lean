module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointSourcePairing
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointAugmentation

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元の全source-frameの要素の始域と次数を、元の全augmentationの添字へ送る。
方針：同じ全要素のパラメーターの二射影と反対積の同じ同値を合成する。
規約：元の試験対象・単体次数・augmentationを変えない。
使われ方：同じ全augmentationの逆を同じ全実射の始域へ引き戻す。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
variable (A : Type u) [CommRing A]
local instance jointSourceParametersModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance jointSourceParametersFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩

/-- 元の全実射の始域と次数を、元の全augmentationの反対添字にする。 -/
def strictBETotJointSourceParameterIndex :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotJointSourceElements A ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameIndex A)ᵒᵖ :=
  _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceElementsDown A ⋙
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.sourceFrameArrowParameters (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrame A)
      (rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)) ⋙
    ((CategoryTheory.Prod.fst ((_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebraᵒᵖ × (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) SimplexCategoryᵒᵖ ⋙
        CategoryTheory.Prod.fst (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebraᵒᵖ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).prod'
      (CategoryTheory.Prod.snd ((_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebraᵒᵖ × (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) SimplexCategoryᵒᵖ)) ⋙
    (prodOpEquiv (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra (D := SimplexCategory)).inverse ⋙
    (AsSmall.up : (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra × SimplexCategory ⥤ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameIndex A).op

/-- 同じ全augmentationの評価の引き戻しは、元の実射の始域そのもの。 -/
theorem strictBETotJointSourceParameterIndex_evaluation :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceParameterIndex A ⋙ (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameEvaluation A).op =
      _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.liftedSourceFrameArrowDomain (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrame A)
        (rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)) := rfl

/-- 同じ全augmentationの定値端の引き戻しは、元の試験対象の射影。 -/
theorem strictBETotJointSourceParameterIndex_constant :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceParameterIndex A ⋙ (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrameConstant A).op =
      _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceElementsProjection A ⋙ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomSourceIndex A := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y f
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  apply Quiver.Hom.unop_inj
  apply ULift.ext
  change ((f.hom.1.down.1).unop ≫ 𝟙 _) = (f.hom.1.down.1).unop
  exact Category.comp_id _
end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
