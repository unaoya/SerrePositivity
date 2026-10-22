module
public import SerrePositivity.KST.Fibration.TransportWitnessPointEvaluation
public import SerrePositivity.KST.Fibration.FunctorIsoComponent

/-! # 同じ表現空間の指定同型の評価を、元の diagramIso の指定成分として回収する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {E B : SSet.{u + 1}} (p : E ⟶ B) [LeftFibration p]
  (e : E _⦋0⦌) (R S : LeftTransportRepresentation p)
  (h : VertexIso (transportWitnessVertex R) (transportWitnessVertex S))

/-- 同じ表現空間の実同型を同時評価し、元の二つの分類値へ端点だけを揃える。 -/
def transportWitnessDiagramValueIso :
    VertexIso (R.diagram.app (Opposite.op ⦋0⦌) (p.app (Opposite.op ⦋0⦌) e))
      (S.diagram.app (Opposite.op ⦋0⦌) (p.app (Opposite.op ⦋0⦌) e)) :=
  (eqToIso (congrArg HomotopyCategory.mk
    (transportWitnessDiagramEvaluation_vertex p e R))).symm ≪≫
      VertexIso.map h (transportWitnessDiagramEvaluation p e) ≪≫
      eqToIso (congrArg HomotopyCategory.mk (transportWitnessDiagramEvaluation_vertex p e S))

variable [Quasicategory B]

/-- 同時評価は、同じ元の diagramIso の指定成分を厳密に回収する。 -/
theorem transportWitnessDiagramValueIso_eq :
    (R.diagramIso S h).app (p.app (Opposite.op ⦋0⦌) e) =
      transportWitnessDiagramValueIso p e R S h := by
  let D := transportWitnessDiagram p
  let J := transportWitnessDiagramEvaluation p e
  let V := evaluateFunctorAt (Y := SpaceInfinity.{u}) (p.app (Opposite.op ⦋0⦌) e)
  let a := R.diagramIso S h
  let b := VertexIso.map h D
  let c := VertexIso.map h J
  have ha : HEq a b := F2.iso_endpoints_heq b
    (congrArg HomotopyCategory.mk (transportWitnessDiagram_vertex R))
    (congrArg HomotopyCategory.mk (transportWitnessDiagram_vertex S))
  have hb : HEq (VertexIso.map a V) (VertexIso.map b V) :=
    F2.mapIso_heq_of_heq (hoFunctor.map V).toFunctor a b
      (congrArg HomotopyCategory.mk (transportWitnessDiagram_vertex R)).symm
      (congrArg HomotopyCategory.mk (transportWitnessDiagram_vertex S)).symm ha
  have hf : (hoFunctor.map D).toFunctor ⋙ (hoFunctor.map V).toFunctor =
      (hoFunctor.map J).toFunctor := by
    rw [← Cat.Hom.comp_toFunctor, ← Functor.map_comp]
    rfl
  have hc : HEq (VertexIso.map b V) c := F2.mapIso_heq_of_functor_eq hf h
  have hd : HEq (transportWitnessDiagramValueIso p e R S h) c :=
    F2.iso_endpoints_heq c
      (congrArg HomotopyCategory.mk (transportWitnessDiagramEvaluation_vertex p e R))
      (congrArg HomotopyCategory.mk (transportWitnessDiagramEvaluation_vertex p e S))
  exact eq_of_heq ((F2.functorIso_app_heq_evaluate a
    (p.app (Opposite.op ⦋0⦌) e)).trans (hb.trans (hc.trans hd.symm)))

/-- 同じ同時評価の順方向射は、元の diagramIso の同じ二胞体の評価成分。 -/
theorem transportWitnessDiagramValueIso_hom :
    (transportWitnessDiagramValueIso p e R S h).hom =
      functorHomEvaluate (R.diagramIso S h).hom (p.app (Opposite.op ⦋0⦌) e) := by
  rw [← transportWitnessDiagramValueIso_eq, functorIso_app_hom_evaluate]

end SerrePositivity.KST.Fibration
