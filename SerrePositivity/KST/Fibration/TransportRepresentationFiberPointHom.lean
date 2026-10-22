module
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

private theorem component_reindex {D X : SSet.{u}} {F G : D ⟶ X}
    (α : FunctorHom F G) {a b : D _⦋0⦌} (hab : a = b) :
    functorHomEvaluate α a ≫
      (eqToIso (congrArg HomotopyCategory.mk
        (congrArg (G.app (Opposite.op ⦋0⦌)) hab))).hom =
      (eqToIso (congrArg HomotopyCategory.mk
        (congrArg (F.app (Opposite.op ⦋0⦌)) hab))).hom ≫ functorHomEvaluate α b := by
  cases hab
  simp only [eqToIso_refl, Iso.refl_hom, Category.id_comp, Category.comp_id]

variable {E B : SSet.{u + 1}} (p : E ⟶ B) [LeftFibration p] (b : B _⦋0⦌)
  (v : (vertexFiber p b) _⦋0⦌)

/-- 元の指定 fiber における pointedMap の点は、元の全空間の点の表示変更だけで回収できる。 -/
theorem transportRepresentationFiberPointHom_normalized (R : LeftTransportRepresentation p) :
    cosliceFiberPointHom (transportRepresentationPointAt p v.val R) ≫
      (eqToIso (congrArg HomotopyCategory.mk
        (congrArg (R.diagram.app (Opposite.op ⦋0⦌))
          (v.property.trans (pinchedConstant_zero b))))).hom =
      cosliceFiberPointHom ((transportRepresentationPointedFiberMap R b).app
        (Opposite.op ⦋0⦌) v) := by
  let t := (transportRepresentationPointedFiberMap R b).app (Opposite.op ⦋0⦌) v
  have hv : t.val = R.pointedMap.app (Opposite.op ⦋0⦌) v.val := rfl
  have he := pointedVertexPointHom_transport t _ hv.symm
    (congrArg (fun f => f.app (Opposite.op ⦋0⦌) v.val) R.pointedMap_projection)
    (congrArg (R.diagram.app (Opposite.op ⦋0⦌))
      (v.property.trans (pinchedConstant_zero b)))
  have hn := congrArg (fun m => m ≫
    (eqToIso (congrArg HomotopyCategory.mk
      (congrArg (R.diagram.app (Opposite.op ⦋0⦌))
        (v.property.trans (pinchedConstant_zero b))))).hom)
    (pointedVertexPointHom_fiber (transportRepresentationPointAt p v.val R))
  have hc := hn.symm
  simp only [Category.assoc] at hc
  exact hc.trans he

variable [Quasicategory B] (R S : LeftTransportRepresentation p)
  (h : VertexIso (transportWitnessVertex R) (transportWitnessVertex S))

/-- 同じ表現空間の実比較は、指定した元の fiber 点と同じ diagramIso の b 成分を結ぶ。 -/
theorem transportRepresentationFiberPointHom_diagramIso :
    cosliceFiberPointHom ((transportRepresentationPointedFiberMap R b).app
      (Opposite.op ⦋0⦌) v) ≫ functorHomEvaluate (R.diagramIso S h).hom b =
      cosliceFiberPointHom ((transportRepresentationPointedFiberMap S b).app
        (Opposite.op ⦋0⦌) v) := by
  let r := eqToIso (congrArg HomotopyCategory.mk
    (congrArg (R.diagram.app (Opposite.op ⦋0⦌))
      (v.property.trans (pinchedConstant_zero b))))
  let s := eqToIso (congrArg HomotopyCategory.mk
    (congrArg (S.diagram.app (Opposite.op ⦋0⦌))
      (v.property.trans (pinchedConstant_zero b))))
  have hR := transportRepresentationFiberPointHom_normalized p b v R
  have hS := transportRepresentationFiberPointHom_normalized p b v S
  have hn := component_reindex (R.diagramIso S h).hom
    (v.property.trans (pinchedConstant_zero b))
  have he := transportRepresentationPointHom_diagramIso p v.val R S h
  calc
    _ = (cosliceFiberPointHom (transportRepresentationPointAt p v.val R) ≫ r.hom) ≫
        functorHomEvaluate (R.diagramIso S h).hom b := by rw [hR]
    _ = cosliceFiberPointHom (transportRepresentationPointAt p v.val R) ≫
        (functorHomEvaluate (R.diagramIso S h).hom (p.app (Opposite.op ⦋0⦌) v.val) ≫
          s.hom) := by rw [Category.assoc, ← hn]
    _ = cosliceFiberPointHom (transportRepresentationPointAt p v.val S) ≫ s.hom := by
      rw [← Category.assoc, he]
    _ = _ := hS

end SerrePositivity.KST.Fibration
