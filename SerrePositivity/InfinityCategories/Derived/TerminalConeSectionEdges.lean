module
public import SerrePositivity.InfinityCategories.Derived.DGRoofSliceVertices
public import SerrePositivity.InfinityCategories.F1B.Roof.RightFibrationTerminalRepresentation

/-!
概要：終対象への全錐切断から実辺を回収し、底への像を slice 表示の値に同定する。
方針：元の錐の一単体と同じ一単体を、端点輸送ごと比較する。
規約：底の正規化後も同じ実辺を使う。使われ方：実評価の関手圏内の射の類の照合。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {E B : SSet.{u}} (t : E _⦋0⦌)
variable (σ : E ⟶ sliceOver (SSet.yonedaEquiv.symm t))
variable (hσ : σ ≫ sliceOverProjection _ = 𝟙 E)
/-- 終対象への切断から、指定始点と終点を持つ同じ実辺を回収する。 -/
def roofTerminalConeSectionEdge (a : E _⦋0⦌) :
    Truncated.Edge (X := (truncation 2).obj E) a t where
  edge := (roofPointSliceVertexEdge (SSet.yonedaEquiv.symm t)
    (σ.app (Opposite.op ⦋0⦌) a)).edge
  src_eq := (roofPointSliceVertexEdge _ _).src_eq.trans
    (ConcreteCategory.congr_hom (NatTrans.congr_app hσ (Opposite.op ⦋0⦌)) a)
  tgt_eq := (roofPointSliceVertexEdge _ _).tgt_eq.trans (SSet.yonedaEquiv.apply_symm_apply t)
/-- 底への表示の値の一単体は、元の同じ切断辺の底への像。 -/
lemma roofTerminalRepresentationMap_transport_edge (p : E ⟶ B)
    (c : (Δ[0] : SSet.{u}) ⟶ B)
    (hc : SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) t) = c) (a : E _⦋0⦌) :
    (roofPointSliceVertexEdge c
      ((roofTerminalRepresentationMap p t σ ≫ (eqToIso (congrArg sliceOver hc)).hom).app
        (Opposite.op ⦋0⦌) a)).edge =
      ((roofTerminalConeSectionEdge t σ hσ a).map ((truncation 2).map p)).edge := by
  change SSet.yonedaEquiv ((joinStdSimplexIso 0 0).inv ≫
    ((eqToIso (congrArg sliceOver hc)).hom.app _
      ((roofTargetSliceMap p t).app _ (σ.app _ a))).val) = _
  rw [roofSliceTransport_val hc, roofTargetSliceMap_val, ← Category.assoc, SSet.yonedaEquiv_comp]
  rfl
/-- 底を正規化した slice 表示の値は、元の同じ切断辺を写した射の類。 -/
lemma roofTerminalRepresentationMap_transport_vertex_arrow (p : E ⟶ B)
    (c : (Δ[0] : SSet.{u}) ⟶ B)
    (hc : SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) t) = c) (a : E _⦋0⦌) :
    Arrow.mk (Truncated.HomotopyCategory.homMk (roofPointSliceVertexEdge c
      ((roofTerminalRepresentationMap p t σ ≫ (eqToIso (congrArg sliceOver hc)).hom).app
        (Opposite.op ⦋0⦌) a))) =
      Arrow.mk ((hoFunctor.map p).toFunctor.map
        (Truncated.HomotopyCategory.homMk (roofTerminalConeSectionEdge t σ hσ a))) := by
  exact Truncated.HomotopyCategory.congr_arrowMk_homMk _ _
    (roofTerminalRepresentationMap_transport_edge t σ hσ p c hc a)
end SerrePositivity.InfinityCategories
