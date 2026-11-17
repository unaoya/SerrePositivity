module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointSourceNativeFiber
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningDiagramHom
/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元の native Hom の同じ全空間の射を、両変数の全変換へ送る。
方針：既存の全 straightening 関手による同じ底上の射の像を使う。
規約：元の射と指定された射影を保つ。弱同値の仮定は追加しない。
使われ方：IS-W2 R03d の全関手同型を構成するための、同じ全変換の射。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open scoped _root_.Simplicial
open _root_.HomotopicalAlgebra
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
variable (A : Type u) [CommRing A]
local instance jointNativeTransformationModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance jointNativeTransformationFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩
local instance jointNativeTransformationProjection : LeftFibration (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomProjection A) :=
  _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomProjection_leftFibration A

/-- 同じ底上の射を元の全分類で送り、同じ raw Hom と native Hom の全変換にする。 -/
def strictBETotJointSourceNativeTransformation
    (m : (simplicialElementsReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)).left ⟶
      _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomTotalSpace A)
    (hm : m ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomProjection A =
      (simplicialElementsReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)).hom) :
    FunctorHom (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRawHomCoherent A) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomCoherent A) :=
  (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRawSourceElementsClassificationIso A).hom ≫
    leftStraighteningInfinityDiagramHom
      (simplicialElementsReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)).hom
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomProjection A) m hm ≫
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomClassificationIso A).hom

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
