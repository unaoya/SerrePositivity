module
public import SerrePositivity.KST.SConstruction.ContractibleDiagramSelections
public import Mathlib.AlgebraicTopology.SimplicialSet.Nerve

/-! # Coherent な図式の恒等頂点と over 圏の比較辺
概要：over 圏の自然な族から対象ごとの値と入力の射に沿う実際の辺を取り出す。
方針：恒等射の頂点と、指定射から恒等射へ向かう over 圏の射を評価する。
規約：辺は同じ自然な族から取り出し、自然性の始点を厳密に回収する。
使われ方：全選択の因子の自然性を元の対象ごとの構造射へ接続する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- over 圏の恒等射の頂点で評価した、対象ごとの選択値。 -/
def diagramSelectionVertex {I : Type u} [SmallCategory I] {D : I ⥤ SSet.{u}}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I ⟶ D) (i : I) : (D.obj i) _⦋0⦌ :=
  (s.app i).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Over.mk (𝟙 i)))

/-- Bousfield–Kan 重みの移送は恒等の over 頂点を指定射の over 頂点へ写す。 -/
lemma bousfieldKanWeight_identity_vertex {I : Type u} [SmallCategory I]
    {i j : I} (h : i ⟶ j) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).map h).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Over.mk (𝟙 i))) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Over.mk h) := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Over.mk ((𝟙 i) ≫ h)) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Over.mk h)
  rw [Category.id_comp]

/-- 自然な族は指定射の over 頂点で元の対象の値の移送を厳密に回収する。 -/
lemma diagramSelectionVertex_transport {I : Type u} [SmallCategory I] {D : I ⥤ SSet.{u}}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I ⟶ D) {i j : I} (h : i ⟶ j) :
    (s.app j).app (Opposite.op ⦋0⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Over.mk h)) =
      (D.map h).app (Opposite.op ⦋0⦌) (diagramSelectionVertex s i) := by
  have hh := ConcreteCategory.congr_hom
    (NatTrans.congr_app (s.naturality h) (Opposite.op ⦋0⦌))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Over.mk (𝟙 i)))
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at hh
  exact (congrArg ((s.app j).app (Opposite.op ⦋0⦌))
    (bousfieldKanWeight_identity_vertex h).symm).trans hh

/-- 指定射の over 対象から恒等射の over 対象へ向かう標準射。 -/
def diagramSelectionOverArrow {I : Type u} [SmallCategory I] {i j : I} (h : i ⟶ j) :
    Over.mk h ⟶ Over.mk (𝟙 j) := Over.homMk h (by simp)

/-- 入力射に沿う元の値の移送と、終域の値を結ぶ同じ over 族の実際の辺。 -/
def diagramSelectionEdge {I : Type u} [SmallCategory I] {D : I ⥤ SSet.{u}}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I ⟶ D) {i j : I} (h : i ⟶ j) :
    (D.obj j).Edge ((D.map h).app (Opposite.op ⦋0⦌) (diagramSelectionVertex s i))
      (diagramSelectionVertex s j) :=
  ((CategoryTheory.nerve.edgeMk (diagramSelectionOverArrow h)).map
    (s.app j)).ofEq (diagramSelectionVertex_transport s h) rfl

/-- 同じ over 族の比較辺の一単体は、元の over 射の評価。 -/
lemma diagramSelectionEdge_edge {I : Type u} [SmallCategory I] {D : I ⥤ SSet.{u}}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I ⟶ D) {i j : I} (h : i ⟶ j) :
    (diagramSelectionEdge s h).edge =
      (s.app j).app (Opposite.op ⦋1⦌) (CategoryTheory.nerve.edgeMk (diagramSelectionOverArrow h)).edge := by
  dsimp only [diagramSelectionEdge, SSet.Edge.ofEq, SSet.Edge.edge, SSet.Edge.toTruncated]
  rfl

/-- 恒等成分を元の選択空間へ戻す比較を通じ、同じ over 辺の始点を元の移送で表す。 -/
def diagramSelectionTransportEdge {I : Type u} [SmallCategory I] {D : I ⥤ SSet.{u}}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I ⟶ D) {i j : I} (h : i ⟶ j)
    {E : SSet.{u}} (e : D.obj i ≅ E) (t : E ⟶ D.obj j) (ht : e.hom ≫ t = D.map h) :
    (D.obj j).Edge
      (t.app (Opposite.op ⦋0⦌) (e.hom.app (Opposite.op ⦋0⦌) (diagramSelectionVertex s i)))
      (diagramSelectionVertex s j) :=
  (diagramSelectionEdge s h).ofEq
    (ConcreteCategory.congr_hom (NatTrans.congr_app ht (Opposite.op ⦋0⦌))
      (diagramSelectionVertex s i)).symm rfl

/-- 恒等成分の表示を戻しても、比較辺の元の一単体は変わらない。 -/
lemma diagramSelectionTransportEdge_edge {I : Type u} [SmallCategory I]
    {D : I ⥤ SSet.{u}} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I ⟶ D)
    {i j : I} (h : i ⟶ j) {E : SSet.{u}} (e : D.obj i ≅ E)
    (t : E ⟶ D.obj j) (ht : e.hom ≫ t = D.map h) :
    (diagramSelectionTransportEdge s h e t ht).edge = (diagramSelectionEdge s h).edge := by
  dsimp only [diagramSelectionTransportEdge, SSet.Edge.ofEq,
    SSet.Edge.edge, SSet.Edge.toTruncated]

end SerrePositivity.KST.SConstruction
