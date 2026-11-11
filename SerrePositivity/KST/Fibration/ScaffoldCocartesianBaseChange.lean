module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.ScaffoldCocartesianBaseChange
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.ScaffoldCocartesianBaseChange
public import SerrePositivity.KST.Fibration.ScaffoldCocartesianClassification
public import SerrePositivity.KST.Fibration.ScaffoldVertexBaseChange

/-! # 元の cocartesian 切断の分類と、実底変換の指定点を同じ scaffold 復元で比較する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

variable {I : Type u} [Category.{u} I] {E B : SSet.{u}} [Quasicategory B]
  (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (k : nerve I ⟶ B)

/-- 同じ cocartesian 切断の Kan 分類を、元の底の実図式へ同じ底変換成分で送る。 -/
def scaffoldCocartesianBaseChangeClassificationIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (cocartesianKanCoherentDiagram (pullback.snd p k))
      ((SSet.uliftFunctor.{u + 1, u}).map k ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram p) :=
  scaffoldCocartesianKanClassificationIso (pullback.snd p k) ≪≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_baseChangeIso p k).symm

/-- 元の section 包含・恒等射評価・実 fiber 底変換の同じ点を保持する分類比較。 -/
theorem scaffoldCocartesianBaseChangeClassificationIso_pointHom (c : I)
    (v : ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram (pullback.snd p k)).obj c) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberVertexEquiv
      ((cocartesianKanDiagram (pullback.snd p k)).obj c)).symm
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app
          ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.cocartesianStrictTransportDiagram (pullback.snd p k)).obj c)).app
            (Opposite.op ⦋0⦌) v)) ≫
      (eqToIso (congrArg HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve_vertex (cocartesianKanDiagram (pullback.snd p k)) c))).inv ≫
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (scaffoldCocartesianBaseChangeClassificationIso p k).hom
        (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)) =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom (scaffoldReconstructionFiberPoint p
      (k.app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cofinalVertexFiberBaseChangeIso p k (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)).hom.app (Opposite.op ⦋0⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportEvaluate (pullback.snd p k) c).app (Opposite.op ⦋0⦌)
          (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportInclusion (pullback.snd p k)).app c).app
            (Opposite.op ⦋0⦌) v)))) := by
  let z := ULift.up.{u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)
  let w := (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportEvaluate (pullback.snd p k) c).app (Opposite.op ⦋0⦌)
    (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianStrictTransportInclusion (pullback.snd p k)).app c).app (Opposite.op ⦋0⦌) v)
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.functorIsoValue (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_baseChangeIso p k) z
  have hc := scaffoldCocartesianKanClassificationIso_pointHom (pullback.snd p k) c v
  have hb := scaffoldPointedReconstruction_baseChange_pointHom p k (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c) w
  have hi := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.recoverPoint e _ _ hb
  have hinv := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.functorIsoValue_inv (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_baseChangeIso p k) z
  rw [hinv] at hi
  have hs := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.appendPoint _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_baseChangeIso p k).inv z) hc
  have he := hs.trans hi
  change _ ≫ _ ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate
    ((scaffoldCocartesianKanClassificationIso (pullback.snd p k)).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftStraighteningInfinityDiagram_baseChangeIso p k).inv) z = _
  rw [_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate_comp]
  exact he

end SerrePositivity.KST.Fibration
