module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.F1.Transport.PointedFamilyPointHom
public import SerrePositivity.InfinityCategories.F1.Transport.WitnessDiagram
public import SerrePositivity.InfinityCategories.F1.StraighteningLeft.SmallUnstraighteningPointFiberEvaluation
public import SerrePositivity.InfinityCategories.F1B.FunctorCategories.FunctorHomEvaluationNaturality

/-! # 同じ表現空間の二つの射影を、元の指定点で同時に評価する -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.F1.Transport
open SerrePositivity.KST.Fibration

variable {E B : SSet.{u + 1}} (p : E ⟶ B) [LeftFibration p] (e : E _⦋0⦌)

/-- 元の同じ表現空間の pointedMap を、元の全空間の指定点で評価する。 -/
def transportWitnessPointedEvaluation : transportWitnessSpace p ⟶ PointedSpaceInfinity.{u} :=
  transportWitnessPointed p ≫ evaluateFunctorAt e

/-- 同じ表現空間の分類図式を、同じ点の元の射影で評価する。 -/
def transportWitnessDiagramEvaluation : transportWitnessSpace p ⟶ SpaceInfinity.{u} :=
  transportWitnessDiagram p ≫ evaluateFunctorAt (p.app (Opposite.op ⦋0⦌) e)

/-- 二つの同時評価は、元の全表現空間上で厳密に可換。 -/
theorem transportWitnessPointedEvaluation_projection :
    transportWitnessPointedEvaluation p e ≫ pointedSpaceProjection =
      transportWitnessDiagramEvaluation p e := by
  unfold transportWitnessPointedEvaluation transportWitnessDiagramEvaluation
  rw [Category.assoc, ← evaluateFunctorAt_post, ← Category.assoc,
    transportWitnessDiagram_condition, Category.assoc, evaluateFunctorAt_precomp]

/-- 元の表現を同じ評価族へ入れると、その同じ pointedMap の実際の値を回収する。 -/
theorem transportWitnessPointedEvaluation_vertex (R : LeftTransportRepresentation p) :
    (transportWitnessPointedEvaluation p e).app (Opposite.op ⦋0⦌) (transportWitnessVertex R) =
      R.pointedMap.app (Opposite.op ⦋0⦌) e := by
  change (evaluateFunctorAt e).app (Opposite.op ⦋0⦌)
    ((transportWitnessPointed p).app (Opposite.op ⦋0⦌) (transportWitnessVertex R)) = _
  rw [transportWitnessPointed_vertex, evaluateFunctorAt_functorVertex]

/-- 同じ表現の分類図式の値も、同じ指定点の射影で厳密に回収する。 -/
theorem transportWitnessDiagramEvaluation_vertex (R : LeftTransportRepresentation p) :
    (transportWitnessDiagramEvaluation p e).app (Opposite.op ⦋0⦌) (transportWitnessVertex R) =
      R.diagram.app (Opposite.op ⦋0⦌) (p.app (Opposite.op ⦋0⦌) e) := by
  change (evaluateFunctorAt (p.app (Opposite.op ⦋0⦌) e)).app (Opposite.op ⦋0⦌)
    ((transportWitnessDiagram p).app (Opposite.op ⦋0⦌) (transportWitnessVertex R)) = _
  rw [transportWitnessDiagram_vertex, evaluateFunctorAt_functorVertex]

/-- 同じ表現空間内の元の射は、同時評価した点の射と分類側の射との自然性を保つ。 -/
theorem transportWitnessPointHom_naturality {v w : (transportWitnessSpace p) _⦋0⦌}
    (m : HomotopyCategory.mk v ⟶ HomotopyCategory.mk w) :
    pointedVertexPointHom ((transportWitnessPointedEvaluation p e).app (Opposite.op ⦋0⦌) v) ≫
      (pointedFamilyProjectionValueIso (transportWitnessPointedEvaluation p e)
        (transportWitnessDiagramEvaluation p e)
        (transportWitnessPointedEvaluation_projection p e) v).hom ≫
      (hoFunctor.map (transportWitnessDiagramEvaluation p e)).toFunctor.map m ≫
      (pointedFamilyProjectionValueIso (transportWitnessPointedEvaluation p e)
        (transportWitnessDiagramEvaluation p e)
        (transportWitnessPointedEvaluation_projection p e) w).inv =
      pointedVertexPointHom ((transportWitnessPointedEvaluation p e).app (Opposite.op ⦋0⦌) w) :=
  pointedFamilyPointHom_naturality_over (transportWitnessPointedEvaluation p e)
    (transportWitnessDiagramEvaluation p e) (transportWitnessPointedEvaluation_projection p e) m

end SerrePositivity.InfinityCategories.F1.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.transportWitnessDiagramEvaluation (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.transportWitnessDiagramEvaluation := _root_.SerrePositivity.InfinityCategories.F1.Transport.transportWitnessDiagramEvaluation

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.transportWitnessDiagramEvaluation_vertex := _root_.SerrePositivity.InfinityCategories.F1.Transport.transportWitnessDiagramEvaluation_vertex

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.transportWitnessPointHom_naturality := _root_.SerrePositivity.InfinityCategories.F1.Transport.transportWitnessPointHom_naturality

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.transportWitnessPointedEvaluation (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.transportWitnessPointedEvaluation := _root_.SerrePositivity.InfinityCategories.F1.Transport.transportWitnessPointedEvaluation

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.transportWitnessPointedEvaluation_projection := _root_.SerrePositivity.InfinityCategories.F1.Transport.transportWitnessPointedEvaluation_projection

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.transportWitnessPointedEvaluation_vertex := _root_.SerrePositivity.InfinityCategories.F1.Transport.transportWitnessPointedEvaluation_vertex
