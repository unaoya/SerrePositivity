module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportWitnessPointEvaluation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.FunctorIsoComponent

/-! # 同じ表現空間の指定同型の評価を、元の diagramIso の指定成分として回収する

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
open _root_.SerrePositivity.KST.Fibration
variable {E B : SSet.{u + 1}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
  (e : E _⦋0⦌) (R S : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p)
  (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessVertex R) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessVertex S))

/-- 同じ表現空間の実同型を同時評価し、元の二つの分類値へ端点だけを揃える。 -/
def transportWitnessDiagramValueIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (R.diagram.app (Opposite.op ⦋0⦌) (p.app (Opposite.op ⦋0⦌) e))
      (S.diagram.app (Opposite.op ⦋0⦌) (p.app (Opposite.op ⦋0⦌) e)) :=
  (eqToIso (congrArg HomotopyCategory.mk
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessDiagramEvaluation_vertex p e R))).symm ≪≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map h (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessDiagramEvaluation p e) ≪≫
      eqToIso (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessDiagramEvaluation_vertex p e S))

variable [Quasicategory B]

/-- 同時評価は、同じ元の diagramIso の指定成分を厳密に回収する。 -/
theorem transportWitnessDiagramValueIso_eq :
    (R.diagramIso S h).app (p.app (Opposite.op ⦋0⦌) e) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessDiagramValueIso p e R S h := by
  let D := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessDiagram p
  let J := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessDiagramEvaluation p e
  let V := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (Y := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u}) (p.app (Opposite.op ⦋0⦌) e)
  let a := R.diagramIso S h
  let b := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map h D
  let c := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map h J
  have ha : HEq a b := _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.iso_endpoints_heq b
    (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessDiagram_vertex R))
    (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessDiagram_vertex S))
  have hb : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map a V) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map b V) :=
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.mapIso_heq_of_heq (hoFunctor.map V).toFunctor a b
      (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessDiagram_vertex R)).symm
      (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessDiagram_vertex S)).symm ha
  have hf : (hoFunctor.map D).toFunctor ⋙ (hoFunctor.map V).toFunctor =
      (hoFunctor.map J).toFunctor := by
    rw [← Cat.Hom.comp_toFunctor, ← Functor.map_comp]
    rfl
  have hc : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map b V) c := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.mapIso_heq_of_functor_eq hf h
  have hd : HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessDiagramValueIso p e R S h) c :=
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.iso_endpoints_heq c
      (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessDiagramEvaluation_vertex p e R))
      (congrArg HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessDiagramEvaluation_vertex p e S))
  exact eq_of_heq ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.functorIso_app_heq_evaluate a
    (p.app (Opposite.op ⦋0⦌) e)).trans (hb.trans (hc.trans hd.symm)))

/-- 同じ同時評価の順方向射は、元の diagramIso の同じ二胞体の評価成分。 -/
theorem transportWitnessDiagramValueIso_hom :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessDiagramValueIso p e R S h).hom =
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (R.diagramIso S h).hom (p.app (Opposite.op ⦋0⦌) e) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessDiagramValueIso_eq, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.functorIso_app_hom_evaluate]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessDiagramValueIso (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.transportWitnessDiagramValueIso := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessDiagramValueIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.transportWitnessDiagramValueIso_eq := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessDiagramValueIso_eq

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.transportWitnessDiagramValueIso_hom := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessDiagramValueIso_hom

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.transportWitnessDiagramValueIso._proof_1 := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportWitnessDiagramValueIso._proof_1
