module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointFirstSpan
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.LiftedSourceFrameElements

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元のBEの全source-frame係数を、同じ全要素圏のnative分類へ送る。
方針：元の両変数の第三図式へ検証済みの全係数比較を適用する。
規約：元のprobe・frame・標的置換・全射を保つ。正本Hom∞との照合は別。
使われ方：R03dの同じ全augmentationとtwisted pairingへの接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
variable (A : Type u) [CommRing A]
local instance jointSourceElementsModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance jointSourceElementsFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩

/-- 元の全probeに同じ関手的source frameを適用した図式。 -/
def strictBETotJointSourceFrame :
    (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra ⥤ SimplexCategory ⥤ (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra :=
  _root_.SerrePositivity.EInfinity.BarrattEccles.framedLimitProbeFunctor A ⋙
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.SimplicialLocalization.modelSourceFrameFamily (C := (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra)).obj

/-- 元の第三のHom図式を、同じ全要素係数として記録する。 -/
def strictBETotJointSourceCoefficients : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A ⥤ SSet.{u+1} :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.liftedSourceFrameCoefficients (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrame A)
    (rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A))

/-- 同じ全係数は元の第三の図式そのもの。 -/
theorem strictBETotJointSourceCoefficients_eq :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A =
      AsSmall.down ⋙ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanDiagram A 3 := rfl

/-- 元の全source-frameのHom単体の全要素圏。 -/
abbrev StrictBETotJointSourceElements := SimplicialTotalElements (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)

/-- 同じ元の全要素圏から元の両変数の底への射影。 -/
def strictBETotJointSourceElementsProjection :
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictBETotJointSourceElements A ⥤ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A :=
  simplicialTotalElementsProjection (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)

/-- 元の全要素のラベルを、同じ元のsource-frameの実射へ戻す。 -/
def strictBETotJointSourceElementsDown :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.liftedSourceFrameElementsDown (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFrame A)
    (rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A))

/-- 元の第三図式を同じ元の全要素圏のnative全分類へつなぐ。 -/
def strictBETotJointSourceElementsClassificationIso :
    FunctorIso (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanCoherent A 3)
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A))).obj
          (Over.mk (nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceElementsProjection A)))).hom) :=
  _root_.SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FrameHom.totalElementsNativeClassificationIso (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)

/-- 元の最初の三辺を含むraw Homから、同じ全要素圏のnative全分類への比較。 -/
def strictBETotJointRawSourceElementsClassificationIso :
    FunctorIso (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRawHomCoherent A)
      (leftStraighteningInfinityDiagram
        ((continuousLeftFibrationReplacement (nerve (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A))).obj
          (Over.mk (nerveMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceElementsProjection A)))).hom) :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointFirstSpanComparison A).trans (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceElementsClassificationIso A)
end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
