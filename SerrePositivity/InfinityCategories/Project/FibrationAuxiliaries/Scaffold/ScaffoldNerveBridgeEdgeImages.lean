module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.ScaffoldNerveFirstEdge

/-!
概要：最初の辺と尾部の各辺は、有限鎖への同じ比較の像に入る。
方針：pushout の二射の計算則と尾部の厳密な因子化を使う。
規約：退化辺を含む元の nerve の一次単体を扱う。
使われ方：高次単体への帰納で欠ける辺の三角形分解。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold

/-- 最初の区間の全ての辺は、同じ pushout 比較の像に属する。 -/
lemma scaffoldFiniteNerveBridge_first_edge_mem (n : ℕ)
    (b : (nerve (ULift.{u} (Fin 2))) _⦋1⦌) :
    (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteFirstEdge n)).app (Opposite.op ⦋1⦌) b ∈
      Set.range ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteNerveBridge n).app (Opposite.op ⦋1⦌)) := by
  let s := stdSimplex.isoNerve.{u} 1
  refine ⟨(pushout.inl (stdSimplex.δ (0 : Fin 2))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (ULift.up (0 : Fin (n + 1)) : ULift.{u} _))).app (Opposite.op ⦋1⦌)
      (s.inv.app (Opposite.op ⦋1⦌) b), ?_⟩
  have h := congrArg (fun f ↦ f.app (Opposite.op ⦋1⦌)
    (s.inv.app (Opposite.op ⦋1⦌) b)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteNerveBridge_inl.{u} n)
  have hi : s.hom.app (Opposite.op ⦋1⦌) (s.inv.app (Opposite.op ⦋1⦌) b) = b :=
    congrArg (fun f ↦ f.app (Opposite.op ⦋1⦌) b) s.inv_hom_id
  exact h.trans (congrArg ((nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteFirstEdge n)).app
    (Opposite.op ⦋1⦌)) hi)

/-- 零を避ける始点を持つ全ての辺は、同じ比較の尾部の像に属する。 -/
lemma scaffoldFiniteNerveBridge_tail_edge_mem (n : ℕ)
    (b : (nerve (ULift.{u} (Fin (n + 2)))) _⦋1⦌)
    (hb : (b.obj 0).down ≠ 0) :
    b ∈ Set.range ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteNerveBridge n).app (Opposite.op ⦋1⦌)) := by
  refine ⟨(pushout.inr (stdSimplex.δ (0 : Fin 2))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (ULift.up (0 : Fin (n + 1)) : ULift.{u} _))).app (Opposite.op ⦋1⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTailFactor b), ?_⟩
  have h := congrArg (fun f ↦ f.app (Opposite.op ⦋1⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTailFactor b)) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteNerveBridge_inr.{u} n)
  exact h.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.scaffoldFiniteTailFactor_comp b hb)

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Scaffold
