module

public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointNativeTransformation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftStraighteningDiagramFiberNaturality

/-!
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
open CategoryTheory SSet HomotopicalAlgebra
open scoped Simplicial
open SerrePositivity.EInfinity.BarrattEccles
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

noncomputable section

namespace SerrePositivity.EInfinity.BarrattEccles

variable (A : Type u) [CommRing A]
local instance jointNativeTransformationEvaluationModel : ModelCategory (operad A).Algebra := modelCategory A
local instance jointNativeTransformationEvaluationFactorization :
    (cofibrations (operad A).Algebra).HasFunctorialFactorization
      (trivialFibrations (operad A).Algebra) := ⟨⟨mappingCofibrantFactorization A⟩⟩
local instance jointNativeTransformationEvaluationProjection : LeftFibration (strictBETotJointNativeHomProjection A) :=
  strictBETotJointNativeHomProjection_leftFibration A

/-- 元の全native変換の同じ評価は、元の両分類同型と同じ実際のfiber射の像の合成。 -/
lemma strictBETotJointSourceNativeTransformation_evaluate
    (m : (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).left ⟶
      strictBETotJointNativeHomTotalSpace A)
    (hm : m ≫ strictBETotJointNativeHomProjection A =
      (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).hom)
    (P : strictBETotJointHomIndex A) :
    let p := (simplicialElementsReplacement (strictBETotJointSourceCoefficients A)).hom
    let q := strictBETotJointNativeHomProjection A
    let b := nerveVertex P
    functorHomEvaluate (strictBETotJointSourceNativeTransformation A m hm) (ULift.up b) =
      functorHomEvaluate (strictBETotJointRawSourceElementsClassificationIso A).hom (ULift.up b) ≫
        (leftStraighteningInfinityDiagram_fiberIso p b).hom ≫
        HomotopyCategory.homMk (coherentNerveEdge
          (show leftFibrationFiberObject b (leftFibrationObjectOf p) ⟶
            leftFibrationFiberObject b (leftFibrationObjectOf q) from vertexFiberMap p q m hm b)) ≫
        (leftStraighteningInfinityDiagram_fiberIso q b).inv ≫
        functorHomEvaluate (strictBETotJointNativeHomClassificationIso A).hom (ULift.up b) := by
  dsimp only
  unfold strictBETotJointSourceNativeTransformation
  rw [functorHomEvaluate_comp, functorHomEvaluate_comp,
    leftStraighteningInfinityDiagramHom_actualFiber_value]
  simp only [Category.assoc]

end SerrePositivity.EInfinity.BarrattEccles

end
