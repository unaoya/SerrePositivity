module

public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointNativeTransformation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningDiagramFiberNaturality

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元の二変数native全変換の評価を、元の両分類同型と同じ実fiber射へ照合する。
方針：元の全変換の定義に評価の合成則と同じ全straighteningの評価則を適用する。
規約：元の射と底の等式を保持し、弱同値を仮定しない。
使われ方：同じ全変換の指定単位の照合。
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open _root_.CategoryTheory _root_.SSet _root_.HomotopicalAlgebra
open scoped _root_.Simplicial
open _root_.SerrePositivity.EInfinity.BarrattEccles
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

noncomputable section

namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot

variable (A : Type u) [CommRing A]
local instance jointNativeTransformationEvaluationModel : ModelCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra := _root_.SerrePositivity.EInfinity.BarrattEccles.modelCategory A
local instance jointNativeTransformationEvaluationFactorization :
    (cofibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra) := ⟨⟨_root_.SerrePositivity.EInfinity.BarrattEccles.mappingCofibrantFactorization A⟩⟩
local instance jointNativeTransformationEvaluationProjection : LeftFibration (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomProjection A) :=
  _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomProjection_leftFibration A

/-- 元の全native変換の同じ評価は、元の両分類同型と同じ実際のfiber射の像の合成。 -/
lemma strictBETotJointSourceNativeTransformation_evaluate
    (m : (simplicialElementsReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)).left ⟶
      _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomTotalSpace A)
    (hm : m ≫ _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomProjection A =
      (simplicialElementsReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)).hom)
    (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    let p := (simplicialElementsReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)).hom
    let q := _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomProjection A
    let b := nerveVertex P
    functorHomEvaluate (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeTransformation A m hm) (ULift.up b) =
      functorHomEvaluate (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointRawSourceElementsClassificationIso A).hom (ULift.up b) ≫
        (leftStraighteningInfinityDiagram_fiberIso p b).hom ≫
        HomotopyCategory.homMk (coherentNerveEdge
          (show leftFibrationFiberObject b (leftFibrationObjectOf p) ⟶
            leftFibrationFiberObject b (leftFibrationObjectOf q) from vertexFiberMap p q m hm b)) ≫
        (leftStraighteningInfinityDiagram_fiberIso q b).inv ≫
        functorHomEvaluate (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomClassificationIso A).hom (ULift.up b) := by
  dsimp only
  unfold _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeTransformation
  rw [functorHomEvaluate_comp, functorHomEvaluate_comp,
    leftStraighteningInfinityDiagramHom_actualFiber_value]
  simp only [Category.assoc]

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot

end
