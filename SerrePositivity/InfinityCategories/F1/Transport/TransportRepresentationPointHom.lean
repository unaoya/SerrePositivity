module

public meta import SerrePositivity.InfinityCategories.Simplicial.DeprecatedAlias
public import SerrePositivity.InfinityCategories.F1.Transport.TransportWitnessDiagramComponent
public import SerrePositivity.InfinityCategories.F1.Transport.PointedVertexPointHom

/-! # 同じ表現空間内の指定同型は、元の pointedMap の点と diagramIso の成分を結ぶ -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.F1.Transport
open SerrePositivity.KST.Fibration
variable {E B : SSet.{u + 1}} (p : E ⟶ B) [LeftFibration p] (e : E _⦋0⦌)

/-- 元の表現の pointedMap の同じ点を、元の分類図式の指定値上の実 fiber 点として読む。 -/
def transportRepresentationPointAt (R : LeftTransportRepresentation p) :
    (vertexFiber pointedSpaceProjection
      (R.diagram.app (Opposite.op ⦋0⦌) (p.app (Opposite.op ⦋0⦌) e))) _⦋0⦌ :=
  ⟨R.pointedMap.app (Opposite.op ⦋0⦌) e, by
    have he := congrArg (fun f => f.app (Opposite.op ⦋0⦌) e) R.pointedMap_projection
    exact he.trans (pinchedConstant_zero _).symm⟩

/-- 同時評価の指定値同型は、元の表現の同じ pointedMap の点の射を回収する。 -/
theorem transportRepresentationPointAt_normalized (R : LeftTransportRepresentation p) :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexPointHom ((_root_.SerrePositivity.InfinityCategories.F1.Transport.transportWitnessPointedEvaluation p e).app (Opposite.op ⦋0⦌)
      (transportWitnessVertex R)) ≫
      (_root_.SerrePositivity.InfinityCategories.F1.Transport.pointedFamilyProjectionValueIso (_root_.SerrePositivity.InfinityCategories.F1.Transport.transportWitnessPointedEvaluation p e)
        (_root_.SerrePositivity.InfinityCategories.F1.Transport.transportWitnessDiagramEvaluation p e) (_root_.SerrePositivity.InfinityCategories.F1.Transport.transportWitnessPointedEvaluation_projection p e)
        (transportWitnessVertex R)).hom ≫
      (eqToIso (congrArg HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.F1.Transport.transportWitnessDiagramEvaluation_vertex p e R))).hom =
      _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.F1.Transport.transportRepresentationPointAt p e R) :=
  _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexPointHom_transport (_root_.SerrePositivity.InfinityCategories.F1.Transport.transportRepresentationPointAt p e R) _
    (_root_.SerrePositivity.InfinityCategories.F1.Transport.transportWitnessPointedEvaluation_vertex p e R)
    (congrArg (fun f => f.app (Opposite.op ⦋0⦌) (transportWitnessVertex R))
      (_root_.SerrePositivity.InfinityCategories.F1.Transport.transportWitnessPointedEvaluation_projection p e))
    (_root_.SerrePositivity.InfinityCategories.F1.Transport.transportWitnessDiagramEvaluation_vertex p e R)

variable [Quasicategory B] (R S : LeftTransportRepresentation p)
  (h : VertexIso (transportWitnessVertex R) (transportWitnessVertex S))

/-- 同じ元の表現比較は、元の実点の射と指定した diagramIso の実成分との合成を保つ。 -/
theorem transportRepresentationPointHom_diagramIso :
    _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.F1.Transport.transportRepresentationPointAt p e R) ≫
      functorHomEvaluate (R.diagramIso S h).hom (p.app (Opposite.op ⦋0⦌) e) =
      _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.F1.Transport.transportRepresentationPointAt p e S) := by
  let H := _root_.SerrePositivity.InfinityCategories.F1.Transport.transportWitnessPointedEvaluation p e
  let J := _root_.SerrePositivity.InfinityCategories.F1.Transport.transportWitnessDiagramEvaluation p e
  let cR := _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedFamilyProjectionValueIso H J
    (_root_.SerrePositivity.InfinityCategories.F1.Transport.transportWitnessPointedEvaluation_projection p e) (transportWitnessVertex R)
  let cS := _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedFamilyProjectionValueIso H J
    (_root_.SerrePositivity.InfinityCategories.F1.Transport.transportWitnessPointedEvaluation_projection p e) (transportWitnessVertex S)
  let bR := eqToIso (congrArg HomotopyCategory.mk
    (_root_.SerrePositivity.InfinityCategories.F1.Transport.transportWitnessDiagramEvaluation_vertex p e R))
  let bS := eqToIso (congrArg HomotopyCategory.mk
    (_root_.SerrePositivity.InfinityCategories.F1.Transport.transportWitnessDiagramEvaluation_vertex p e S))
  let vR := _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexPointHom (H.app (Opposite.op ⦋0⦌) (transportWitnessVertex R))
  let vS := _root_.SerrePositivity.InfinityCategories.F1.Transport.pointedVertexPointHom (H.app (Opposite.op ⦋0⦌) (transportWitnessVertex S))
  let m := (hoFunctor.map J).toFunctor.map h.hom
  have hn := _root_.SerrePositivity.InfinityCategories.F1.Transport.transportWitnessPointHom_naturality p e h.hom
  change vR ≫ cR.hom ≫ m ≫ cS.inv = vS at hn
  have hR : vR ≫ cR.hom ≫ bR.hom =
      _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.F1.Transport.transportRepresentationPointAt p e R) :=
    _root_.SerrePositivity.InfinityCategories.F1.Transport.transportRepresentationPointAt_normalized p e R
  have hS : vS ≫ cS.hom ≫ bS.hom =
      _root_.SerrePositivity.InfinityCategories.F1.Transport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.F1.Transport.transportRepresentationPointAt p e S) :=
    _root_.SerrePositivity.InfinityCategories.F1.Transport.transportRepresentationPointAt_normalized p e S
  have hc : vR ≫ cR.hom ≫ m ≫ bS.hom = vS ≫ cS.hom ≫ bS.hom := by
    have he := congrArg (fun f => f ≫ cS.hom ≫ bS.hom) hn
    simpa only [Category.assoc, Iso.inv_hom_id_assoc] using he
  have hm : functorHomEvaluate (R.diagramIso S h).hom (p.app (Opposite.op ⦋0⦌) e) =
      bR.inv ≫ m ≫ bS.hom := by
    rw [← _root_.SerrePositivity.InfinityCategories.F1.Transport.transportWitnessDiagramValueIso_hom]
    rfl
  calc
    _ = (vR ≫ cR.hom ≫ bR.hom) ≫ (bR.inv ≫ m ≫ bS.hom) := by rw [hR, hm]
    _ = vR ≫ cR.hom ≫ m ≫ bS.hom := by
      simp only [Category.assoc, Iso.hom_inv_id_assoc]
    _ = _ := hc.trans hS

end SerrePositivity.InfinityCategories.F1.Transport

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section

@[deprecated _root_.SerrePositivity.InfinityCategories.F1.Transport.transportRepresentationPointAt (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.transportRepresentationPointAt := _root_.SerrePositivity.InfinityCategories.F1.Transport.transportRepresentationPointAt

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.transportRepresentationPointAt_normalized := _root_.SerrePositivity.InfinityCategories.F1.Transport.transportRepresentationPointAt_normalized

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.transportRepresentationPointHom_diagramIso := _root_.SerrePositivity.InfinityCategories.F1.Transport.transportRepresentationPointHom_diagramIso

@[deprecated (since := "2026-11-05")]
deprecated_alias _root_.SerrePositivity.KST.Fibration.transportRepresentationPointAt._proof_1 := _root_.SerrePositivity.InfinityCategories.F1.Transport.transportRepresentationPointAt._proof_1
