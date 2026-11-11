module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.TransportRepresentationFiberPointHom
import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.TransportRepresentationFiberPointHom
public import SerrePositivity.KST.Fibration.ChosenRepresentationPointHom
public import SerrePositivity.KST.Fibration.NativeRepresentationPoint

/-! # 同じ指定 fiber の実点において、表現比較の diagramIso 成分との自然性を保つ -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

variable {E B : SSet.{u + 1}} (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p] (b : B _⦋0⦌)
  (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber p b) _⦋0⦌)

/-- 元の指定 fiber における pointedMap の点は、元の全空間の点の表示変更だけで回収できる。 -/
theorem transportRepresentationFiberPointHom_normalized (R : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportRepresentationPointAt p v.val R) ≫
      (eqToIso (congrArg HomotopyCategory.mk
        (congrArg (R.diagram.app (Opposite.op ⦋0⦌))
          (v.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero b))))).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom ((transportRepresentationPointedFiberMap R b).app
        (Opposite.op ⦋0⦌) v) := by
  let t := (transportRepresentationPointedFiberMap R b).app (Opposite.op ⦋0⦌) v
  have hv : t.val = R.pointedMap.app (Opposite.op ⦋0⦌) v.val := rfl
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointedVertexPointHom_transport t _ hv.symm
    (congrArg (fun f => f.app (Opposite.op ⦋0⦌) v.val) R.pointedMap_projection)
    (congrArg (R.diagram.app (Opposite.op ⦋0⦌))
      (v.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero b)))
  have hn := congrArg (fun m => m ≫
    (eqToIso (congrArg HomotopyCategory.mk
      (congrArg (R.diagram.app (Opposite.op ⦋0⦌))
        (v.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero b))))).hom)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.pointedVertexPointHom_fiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportRepresentationPointAt p v.val R))
  have hc := hn.symm
  simp only [Category.assoc] at hc
  exact hc.trans he

variable [Quasicategory B] (R S : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.LeftTransportRepresentation p)
  (h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessVertex R) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.transportWitnessVertex S))

/-- 同じ表現空間の実比較は、指定した元の fiber 点と同じ diagramIso の b 成分を結ぶ。 -/
theorem transportRepresentationFiberPointHom_diagramIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom ((transportRepresentationPointedFiberMap R b).app
      (Opposite.op ⦋0⦌) v) ≫ _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (R.diagramIso S h).hom b =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom ((transportRepresentationPointedFiberMap S b).app
        (Opposite.op ⦋0⦌) v) := by
  let r := eqToIso (congrArg HomotopyCategory.mk
    (congrArg (R.diagram.app (Opposite.op ⦋0⦌))
      (v.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero b))))
  let s := eqToIso (congrArg HomotopyCategory.mk
    (congrArg (S.diagram.app (Opposite.op ⦋0⦌))
      (v.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero b))))
  have hR := transportRepresentationFiberPointHom_normalized p b v R
  have hS := transportRepresentationFiberPointHom_normalized p b v S
  have hn := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.component_reindex (R.diagramIso S h).hom
    (v.property.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero b))
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportRepresentationPointHom_diagramIso p v.val R S h
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportRepresentationPointAt p v.val R) ≫ r.hom) ≫
        _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (R.diagramIso S h).hom b := by rw [hR]
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportRepresentationPointAt p v.val R) ≫
        (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (R.diagramIso S h).hom (p.app (Opposite.op ⦋0⦌) v.val) ≫
          s.hom) := by rw [Category.assoc, ← hn]
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportRepresentationPointAt p v.val S) ≫ s.hom := by
      rw [← Category.assoc, he]
    _ = _ := hS

end SerrePositivity.KST.Fibration
