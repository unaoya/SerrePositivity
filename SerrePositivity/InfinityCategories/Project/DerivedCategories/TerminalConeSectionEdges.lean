module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.DGRoofSliceVertices
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibrationTerminalRepresentation

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
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
variable {E B : SSet.{u}} (t : E _⦋0⦌)
variable (σ : E ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver (SSet.yonedaEquiv.symm t))
variable (hσ : σ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection _ = 𝟙 E)
/-- 終対象への切断から、指定始点と終点を持つ同じ実辺を回収する。 -/
def roofTerminalConeSectionEdge (a : E _⦋0⦌) :
    Truncated.Edge (X := (truncation 2).obj E) a t where
  edge := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge (SSet.yonedaEquiv.symm t)
    (σ.app (Opposite.op ⦋0⦌) a)).edge
  src_eq := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge _ _).src_eq.trans
    (ConcreteCategory.congr_hom (NatTrans.congr_app hσ (Opposite.op ⦋0⦌)) a)
  tgt_eq := (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge _ _).tgt_eq.trans (SSet.yonedaEquiv.apply_symm_apply t)
/-- 底への表示の値の一単体は、元の同じ切断辺の底への像。 -/
lemma roofTerminalRepresentationMap_transport_edge (p : E ⟶ B)
    (c : (Δ[0] : SSet.{u}) ⟶ B)
    (hc : SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) t) = c) (a : E _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge c
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.roofTerminalRepresentationMap p t σ ≫ (eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver hc)).hom).app
        (Opposite.op ⦋0⦌) a)).edge =
      ((roofTerminalConeSectionEdge t σ hσ a).map ((truncation 2).map p)).edge := by
  change SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso 0 0).inv ≫
    ((eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver hc)).hom.app _
      ((_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetSliceMap p t).app _ (σ.app _ a))).val) = _
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.roofSliceTransport_val hc, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Roof.roofTargetSliceMap_val, ← Category.assoc, SSet.yonedaEquiv_comp]
  rfl
/-- 底を正規化した slice 表示の値は、元の同じ切断辺を写した射の類。 -/
lemma roofTerminalRepresentationMap_transport_vertex_arrow (p : E ⟶ B)
    (c : (Δ[0] : SSet.{u}) ⟶ B)
    (hc : SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) t) = c) (a : E _⦋0⦌) :
    Arrow.mk (Truncated.HomotopyCategory.homMk (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.roofPointSliceVertexEdge c
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.roofTerminalRepresentationMap p t σ ≫ (eqToIso (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver hc)).hom).app
        (Opposite.op ⦋0⦌) a))) =
      Arrow.mk ((hoFunctor.map p).toFunctor.map
        (Truncated.HomotopyCategory.homMk (roofTerminalConeSectionEdge t σ hσ a))) := by
  exact Truncated.HomotopyCategory.congr_arrowMk_homMk _ _
    (roofTerminalRepresentationMap_transport_edge t σ hσ p c hc a)
end SerrePositivity.InfinityCategories.Project.DerivedCategories
