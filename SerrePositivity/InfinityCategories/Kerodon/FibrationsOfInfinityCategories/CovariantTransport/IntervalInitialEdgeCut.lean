module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinInitialHornLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.InvertibleEdgeLifting

/-!
概要：最初の辺が非退化な区間の単体の切断の計算。
方針：最初の二頂点の値を読み、単調性から残りの頂点の時刻を決める。
規約：区間の標準辺は恒等一単体で表す。
使われ方：Kerodon Proposition 5.2.3.15（Tag 024J）、相対 join の外ホーンの時間条件。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：最初の辺が零から一へ進む区間の単体の切断は一。
方針：自然性で最初の二頂点の値を取り出し、それ以降には単調性を使う。
規約：最初の辺は零番目の外ホーンの標準辺を包含したもの。
使われ方：Kerodon Proposition 5.2.3.15（Tag 024J）、標準 prism の垂直辺から切断一を得る。 -/
lemma intervalHom_cut_one_of_initial_edge (n : ℕ)
    (b : (Δ[n + 2] : SSet.{u}) ⟶ Δ[1])
    (hb : b.app (Opposite.op ⦋1⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge n).val =
      stdSimplex.objEquiv.symm (𝟙 ⦋1⦌)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv b)).toOrderHom 1 = 1 := by
  have he : (Δ[1] : SSet.{u}).map (stdSimplex.objEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge n).val).op
      (SSet.yonedaEquiv b) = stdSimplex.objEquiv.symm (𝟙 ⦋1⦌) := by
    have hh := stdSimplex.map_objEquiv_op_apply (SSet.yonedaEquiv b) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.initialHornEdge n).val
    simpa only [Equiv.symm_apply_apply, hb] using hh
  have h0 : SSet.yonedaEquiv b (0 : Fin (n + 3)) = 0 := by
    have hh := congrArg (fun z : (Δ[1] : SSet.{u}) _⦋1⦌ ↦ z 0) he
    exact hh
  have h1 : SSet.yonedaEquiv b (1 : Fin (n + 3)) = 1 := by
    have hh := congrArg (fun z : (Δ[1] : SSet.{u}) _⦋1⦌ ↦ z 1) he
    exact hh
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.cut_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le _ _) (by omega)
  intro i
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff]
  change ((SSet.yonedaEquiv b) i).val < 1 ↔ i.val < 1
  by_cases hi : i = 0
  · subst i
    rw [h0]
    simp
  · have hi' : (1 : Fin (n + 3)) ≤ i := by
      change 1 ≤ i.val
      have := Fin.pos_iff_ne_zero.mpr hi
      omega
    have hm := (stdSimplex.objEquiv (SSet.yonedaEquiv b)).toOrderHom.monotone hi'
    change SSet.yonedaEquiv b 1 ≤ SSet.yonedaEquiv b i at hm
    rw [h1] at hm
    have hi'' : 0 < i.val := Fin.pos_iff_ne_zero.mpr hi
    change 1 ≤ ((SSet.yonedaEquiv b) i).val at hm
    omega

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
