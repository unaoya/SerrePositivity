module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting

/-!
概要：左ファイブレーションで辺の両端を固定し、像を同じ類の指定辺へ揃える。
方針：像の類の等式を退化最初辺を持つ二単体にし、同じ二単体を持ち上げる。
規約：元の辺のホモトピー類と両端を保持する。
使われ方：共有頂点での同型の一致から整合する全パラメーターの path を作る。

対応節は Kerodon 5.1（Tag 01T1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations

/-- 同じ像の類を持つ指定辺に合わせ、両端と元の類を保って代表辺を変更できる。 -/
lemma leftFibration_exists_edge_representative_over
    {X Y : SSet.{u}} [Quasicategory Y] (q : X ⟶ Y) [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration q]
    {x y : X _⦋0⦌}
    (e : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (d : SSet.Truncated.Edge (X := (truncation 2).obj Y)
      (q.app (Opposite.op ⦋0⦌) x) (q.app (Opposite.op ⦋0⦌) y))
    (h : SSet.Truncated.HomotopyCategory.homMk d =
      SSet.Truncated.HomotopyCategory.homMk (e.map ((truncation 2).map q))) :
    ∃ e' : SSet.Truncated.Edge (X := (truncation 2).obj X) x y,
      e'.map ((truncation 2).map q) = d ∧
      SSet.Truncated.HomotopyCategory.homMk e' =
        SSet.Truncated.HomotopyCategory.homMk e := by
  let i := SSet.Truncated.Edge.id (X := (truncation 2).obj X) x
  have hf : SSet.Truncated.HomotopyCategory.homMk (i.map ((truncation 2).map q)) ≫
      SSet.Truncated.HomotopyCategory.homMk d =
      SSet.Truncated.HomotopyCategory.homMk (e.map ((truncation 2).map q)) := by
    simpa only [i, SSet.Truncated.Edge.map_id,
      SSet.Truncated.HomotopyCategory.homMk_id, Category.id_comp] using h
  obtain ⟨t⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.compStruct_nonempty_of_homMk_fac hf
  obtain ⟨e', t', ht⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.leftFibration_liftCompStruct q i e d t
  refine ⟨e', ?_, ?_⟩
  · apply SSet.Truncated.Edge.ext
    change q.app (Opposite.op ⦋1⦌) e'.edge = d.edge
    rw [← t'.d₀]
    calc
      _ = Y.δ 0 (q.app (Opposite.op ⦋2⦌) t'.simplex) :=
        ConcreteCategory.congr_hom (q.naturality (SimplexCategory.δ 0).op) t'.simplex
      _ = d.edge := by rw [ht]; exact t.d₀
  · simpa only [i, SSet.Truncated.HomotopyCategory.homMk_id, Category.id_comp] using
      SSet.Truncated.HomotopyCategory.homMk_comp_homMk t'

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations
