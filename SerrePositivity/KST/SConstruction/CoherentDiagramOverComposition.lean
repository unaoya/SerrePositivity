module
public import SerrePositivity.KST.SConstruction.CoherentDiagramOverEdges

/-! # 同じ over 族から得る比較辺の合成三角形
概要：同じ自然な over 族の二つの比較辺と合成射の比較辺を実三角形へ束ねる。
方針：over 圏の実際の可換三角形を元の評価族で写す。
規約：標的の Kan 性も辺の選び直しも要求しない。
使われ方：全射列の選択を実際の比較辺と高次の整合性へ接続する。
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

/-- 重みの移送は over 射の実際の一単体も保持する。 -/
lemma bousfieldKanWeight_overArrow_edge {I : Type u} [SmallCategory I]
    {i j k : I} (h : i ⟶ j) (g : j ⟶ k) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I).map g).app (Opposite.op ⦋1⦌)
        (CategoryTheory.nerve.edgeMk (diagramSelectionOverArrow h)).edge =
      (CategoryTheory.nerve.edgeMk ((Over.map g).map (diagramSelectionOverArrow h))).edge :=
  nerveMap_app_mk₁ (Over.map g) (diagramSelectionOverArrow h)

/-- 前の比較辺を後の入力で写し、合成射の始点を厳密に回収する。 -/
def diagramSelectionCompositionFirstEdge {I : Type u} [SmallCategory I] {D : I ⥤ SSet.{u}}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I ⟶ D) {i j k : I} (h : i ⟶ j) (g : j ⟶ k) :
    (D.obj k).Edge ((D.map (h ≫ g)).app (Opposite.op ⦋0⦌) (diagramSelectionVertex s i))
      ((D.map g).app (Opposite.op ⦋0⦌) (diagramSelectionVertex s j)) :=
  ((diagramSelectionEdge s h).map (D.map g)).ofEq
    (ConcreteCategory.congr_hom (NatTrans.congr_app (D.map_comp h g) (Opposite.op ⦋0⦌))
      (diagramSelectionVertex s i)).symm rfl

/-- 同じ over 族から得る指定した二つの比較辺は、合成射の比較辺と実三角形をなす。 -/
lemma diagramSelectionCompositionTriangle_nonempty {I : Type u} [SmallCategory I]
    {D : I ⥤ SSet.{u}} (s : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.bousfieldKanWeight I ⟶ D)
    {i j k : I} (h : i ⟶ j) (g : j ⟶ k) :
    Nonempty (SSet.Edge.CompStruct (diagramSelectionCompositionFirstEdge s h g)
      (diagramSelectionEdge s g) (diagramSelectionEdge s (h ≫ g))) := by
  let a := (Over.map g).map (diagramSelectionOverArrow h)
  let b := diagramSelectionOverArrow ((𝟙 j) ≫ g)
  let c := diagramSelectionOverArrow (h ≫ g)
  have hab : a ≫ b = c := by
    apply Over.OverMorphism.ext
    change h ≫ ((𝟙 j) ≫ g) = h ≫ g
    rw [Category.id_comp]
  obtain ⟨t⟩ := (CategoryTheory.nerve.nonempty_compStruct_iff a b c).mpr hab
  have hn := ConcreteCategory.congr_hom
    (NatTrans.congr_app (s.naturality g) (Opposite.op ⦋1⦌))
    (CategoryTheory.nerve.edgeMk (diagramSelectionOverArrow h)).edge
  simp only [NatTrans.comp_app, ConcreteCategory.comp_apply] at hn
  have ha : ((CategoryTheory.nerve.edgeMk a).map (s.app k)).edge =
      (diagramSelectionCompositionFirstEdge s h g).edge := by
    have ht := congrArg ((s.app k).app (Opposite.op ⦋1⦌))
      (bousfieldKanWeight_overArrow_edge h g).symm
    have he := congrArg ((D.map g).app (Opposite.op ⦋1⦌)) (diagramSelectionEdge_edge s h).symm
    exact ht.trans (hn.trans he)
  have hb : ((CategoryTheory.nerve.edgeMk b).map (s.app k)).edge =
      (diagramSelectionEdge s g).edge := by
    have he := congrArg (fun q : j ⟶ k =>
      ((CategoryTheory.nerve.edgeMk (diagramSelectionOverArrow q)).map (s.app k)).edge)
      (Category.id_comp g)
    exact he.trans (diagramSelectionEdge_edge s g).symm
  exact ⟨(t.map (s.app k)).ofEq ha hb rfl⟩

end SerrePositivity.KST.SConstruction
