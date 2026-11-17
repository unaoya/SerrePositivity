module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointSourcePairing
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotModelWeakTransformation

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元のBEの標的置換単位を全図式で反転し、同じ全実射の標的から元の標的へ戻す。
方針：元のright-frame置換単位を同じモデル源へ送り、元の全要素の射影へ前合成する。
規約：元の単位と元のモデル源の同じ全関手同型を使う。
使われ方：R03dの同じpairingの標的端点の正規化。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
variable (A : Type u) [CommRing A]
local instance jointTargetReplacementModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance jointTargetReplacementFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩

/-- 同じ元の標的置換を、元のモデル源の通常の添字にする。 -/
def strictBETotTargetReplacement :
    AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⥤ AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra :=
  AsSmall.down ⋙ rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A) ⋙ AsSmall.up

/-- 元の標的置換単位を同じ全添字で記録する。 -/
def strictBETotTargetReplacementUnit :
    𝟭 (AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) ⟶ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTargetReplacement A :=
  Functor.whiskerRight
    (Functor.whiskerLeft AsSmall.down (rightFrameReplacementUnit (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A))) AsSmall.up

/-- 同じ元の標的置換単位は全モデル弱同値。 -/
theorem strictBETotTargetReplacementUnit_weak (Y : AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) :
    weakEquivalences (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra
      (AsSmall.down.map ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTargetReplacementUnit A).app Y)) :=
  (rightFrameReplacementUnit_trivialCofibration (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A) (AsSmall.down.obj Y)).2

/-- 元の全標的置換単位自身を同じモデル源で反転する全関手同型。 -/
def strictBETotTargetReplacementNativeIso :
    FunctorIso (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A)
      (nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTargetReplacement A) ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A) := by
  have h := _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelWeakTransformationIso A
    (F := 𝟭 (AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)) (G := _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTargetReplacement A)
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTargetReplacementUnit A) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTargetReplacementUnit_weak A)
  have hi : nerveMap (𝟭 (AsSmall.{u+1} (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)) = 𝟙 _ := rfl
  rw [hi, Category.id_comp] at h
  exact h

/-- 元の実射の標的は、元の全標的射影に同じ置換を合成したもの。 -/
theorem strictBETotJointSourceCodomain_replacement :
    _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.liftedSourceFrameArrowCodomain (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrame A)
      (rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)) =
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceElementsProjection A ⋙ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomTargetIndex A ⋙
      _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTargetReplacement A := rfl

/-- 元の全実射のnativeな標的の全図式。 -/
def strictBETotJointSourceNativeCodomain :
    nerve (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotJointSourceElements A) ⟶ _root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A :=
  nerveMap (_root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.liftedSourceFrameArrowCodomain (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrame A)
    (rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A))) ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A

/-- 同じ全実射の元の標的のnativeな全図式。 -/
def strictBETotJointSourceOriginalNativeCodomain :
    nerve (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotJointSourceElements A) ⟶ _root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A :=
  nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceElementsProjection A ⋙ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomTargetIndex A) ≫
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A

/-- 元の全標的置換単位の同じ逆を、元の全実射の標的へ引き戻した比較。 -/
def strictBETotJointSourceTargetReplacementIso :
    FunctorIso (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeCodomain A)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceOriginalNativeCodomain A) := by
  have h := (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTargetReplacementNativeIso A).precomp
    (nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceElementsProjection A ⋙ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomTargetIndex A))
  change FunctorIso (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceOriginalNativeCodomain A)
    (nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceElementsProjection A ⋙ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomTargetIndex A ⋙
      _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotTargetReplacement A) ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A) at h
  rw [← _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCodomain_replacement] at h
  exact h.symm
end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
