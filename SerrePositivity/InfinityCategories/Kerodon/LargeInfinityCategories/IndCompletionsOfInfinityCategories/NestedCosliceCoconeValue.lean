module

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.DiagramNestedCoslice

/-!
概要：展開した図式の同じ余錐を coslice 内へ戻したときの値写像と頂点。
方針：既存の結合同型と curry の射影公式で、元の全空間の余錐への因子分解を照合する。
規約：余錐の指定頂点と元の値写像を厳密に保持する。
使われ方：cofinal 性の有限余錐の値と添字の頂点を一致させる。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
variable {P K X : SSet.{u}} {p : P ⟶ X} (f : K ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p)
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry f))

/-- 同じ coslice 余錐の値写像は元の展開余錐への指定された前合成。 -/
lemma nestedCosliceCocone_value :
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.diagramNestedCosliceDiagramCurry f Δ[0] c).val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr P (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0]) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinAssociator P K Δ[0]).inv ≫ c.val := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.diagramNestedCosliceDiagramCurry]
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceUnderCurry_projection]

/-- 同じ値写像の像は元の展開余錐の像に含まれる。 -/
lemma nestedCosliceCocone_value_range_le :
    Subcomplex.range ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.diagramNestedCosliceDiagramCurry f Δ[0] c).val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) ≤
      Subcomplex.range c.val := by
  rw [nestedCosliceCocone_value]
  exact Subfunctor.range_comp_le (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr P (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0]) ≫
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinAssociator P K Δ[0]).inv) c.val

/-- 右頂点上の値は、展開した元の余錐の同じ頂点に厳密に一致する。 -/
lemma nestedCosliceCocone_vertex :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p).app _
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex (p := f) (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.diagramNestedCosliceDiagramCurry f Δ[0] c)) =
      c.vertex := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K Δ[0] ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr P (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K Δ[0]) ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinAssociator P K Δ[0]).inv = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join P K) Δ[0] := by
    rw [← Category.assoc, ← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.stableJoinAssociator_inr, Category.assoc,
      Iso.hom_inv_id, Category.comp_id]
  have hv : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K Δ[0] ≫
      ((_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.diagramNestedCosliceDiagramCurry f Δ[0] c).val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join P K) Δ[0] ≫ c.val := by
    rw [nestedCosliceCocone_value]
    exact (congrArg (fun a => a ≫ c.val) he)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_eq, ← SSet.yonedaEquiv_comp, Category.assoc, hv]
  rfl

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
