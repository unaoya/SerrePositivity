module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.StrictRightStraighteningFiberDiagram
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.StrictRightFibrationFiberNative
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanOppositeCoefficients
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.KanDiagramNaturalTransformation

/-!
概要：right straightening で評価される反転 fiber 図式は、元の fiber 図式の反転と自然同型。
方針：実際の fiber 反転同型を各段に取り、元の底上の射に対する自然性を確認する。
規約：各段の頂点だけでなく、元の通常の全図式の射を保つ。
使われ方：証明済みの strict fiber 余極限を前層の評価余極限へ接続する。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {B : SSet.{u}} {I : Type u} [SmallCategory I]

/-- 元の各 fiber の反転と、反転した射影の同じ fiber の図式の自然同型。 -/
def rightFibrationOppositeFiberDiagramIso (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B) (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationFiberKanDiagram F b ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor ≅
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationOppositeFiberDiagram F (SSet.opObjEquiv.symm b) :=
  NatIso.ofComponents (fun i => {
    hom := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.vertexFiberOpIso (F.obj i).val.hom b).hom
    inv := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.vertexFiberOpIso (F.obj i).val.hom b).inv
    hom_inv_id := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.vertexFiberOpIso (F.obj i).val.hom b).hom_inv_id
    inv_hom_id := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.vertexFiberOpIso (F.obj i).val.hom b).inv_hom_id }) (by
    intro i j f
    change SSet.opFunctor.map ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationFiberDiagram F b).map f) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.vertexFiberOpIso (F.obj j).val.hom b).hom =
        (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.vertexFiberOpIso (F.obj i).val.hom b).hom ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentEnrichedUnderlyingFunctor
            (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftFibrationFiberEvaluationEnriched (SSet.opObjEquiv.symm b))).map
              ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationOppositeOrdinary B).map (F.map f))
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.leftFiberEvaluation_underlying_map]
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro x
    apply Subtype.ext
    rfl)

/-- 元の right straightening の全評価図式を、元の right fiber 図式の反転へ直接比較する。 -/
def strictRightStraighteningOriginalFiberDiagramIso (F : I ⥤ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.RightFibrationObject B)
    (b : B _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.rightStraighteningInfinityMap B ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (ULift.up (SSet.opObjEquiv.symm b)))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationFiberKanDiagram F b ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor)) := by
  let e := rightFibrationOppositeFiberDiagramIso F b
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramFunctorIsoOfPointwise
    (F := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationFiberKanDiagram F b ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanObjectOpFunctor, trivial⟩)
    (G := ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.rightFibrationOppositeFiberDiagram F (SSet.opObjEquiv.symm b), trivial⟩)
    (Functor.whiskerRight e.hom _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanObjectForget)
    (fun i => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.qCatEquivalenceOfIso (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.vertexFiberOpIso (F.obj i).val.hom b)).isQCatEquivalence)
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.strictRightStraighteningFiberDiagramIso F (SSet.opObjEquiv.symm b) ≪≫ he.symm

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
