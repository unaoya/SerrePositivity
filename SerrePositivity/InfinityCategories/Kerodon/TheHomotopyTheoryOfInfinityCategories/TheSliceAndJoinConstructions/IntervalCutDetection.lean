module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinIntervalProjection

/-!
概要：区間の単体と標準単体から区間への射を切断で判定する。
方針：値零の逆像が切断であることと区間の二つの値だけを使う。
規約：切断は零を値に取る頂点数。
使われ方：Kerodon Proposition 4.3.3.24（Tag 02QU）、join の内ホーンの時間の分類。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：区間の二つの単体は切断が同じなら等しい。
方針：各頂点で値が一未満となる条件を比較し、値が零か一であることを使う。
規約：n は単体の次数。
使われ方：Kerodon Proposition 4.3.3.24（Tag 02QU）、貼り合わせた単体が指定時間を持つことの確認。 -/
lemma intervalSimplex_eq_of_pullCut_eq {n : ℕ} (s t : (Δ[1] : SSet.{u}) _⦋n⦌)
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv s).toOrderHom 1 =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv t).toOrderHom 1) : s = t := by
  apply stdSimplex.ext
  intro j
  apply Fin.ext
  have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff (stdSimplex.objEquiv s).toOrderHom 1 j
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff (stdSimplex.objEquiv t).toOrderHom 1 j
  rw [hc] at hs
  change j.val < _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv t).toOrderHom 1 ↔ (s j).val < 1 at hs
  change j.val < _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv t).toOrderHom 1 ↔ (t j).val < 1 at ht
  have hsj := (s j).isLt
  have htj := (t j).isLt
  omega

/-- 概要：切断が零である区間への標準単体の射は一頂点に定値。
方針：零を値に取る頂点が存在しないことを各頂点で使う。
規約：射の等式として述べる。
使われ方：Kerodon Proposition 4.3.3.24（Tag 02QU）、join の右因子だけのホーン。 -/
lemma intervalHom_eq_const_one_of_cut_zero {n : ℕ} (t : (Δ[n] : SSet.{u}) ⟶ Δ[1])
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 = 0) :
    t = SSet.const (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
  apply SSet.yonedaEquiv.injective
  apply stdSimplex.ext
  intro j
  apply Fin.ext
  have hj := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 j
  rw [hc] at hj
  change j.val < 0 ↔ ((SSet.yonedaEquiv t) j).val < 1 at hj
  change ((SSet.yonedaEquiv t) j).val = 1
  have ht := ((SSet.yonedaEquiv t) j).isLt
  omega

/-- 概要：切断が全頂点数である区間への標準単体の射は零頂点に定値。
方針：全ての頂点の値が一未満であることを使う。
規約：射の等式として述べる。
使われ方：Kerodon Proposition 4.3.3.24（Tag 02QU）、join の左因子だけのホーン。 -/
lemma intervalHom_eq_const_zero_of_cut_all {n : ℕ} (t : (Δ[n] : SSet.{u}) ⟶ Δ[1])
    (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 = n + 1) :
    t = SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  apply SSet.yonedaEquiv.injective
  apply stdSimplex.ext
  intro j
  apply Fin.ext
  have hj := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.lt_pullCut_iff (stdSimplex.objEquiv (SSet.yonedaEquiv t)).toOrderHom 1 j
  rw [hc] at hj
  change j.val < n + 1 ↔ ((SSet.yonedaEquiv t) j).val < 1 at hj
  have hlt := hj.mp j.isLt
  change ((SSet.yonedaEquiv t) j).val = 0
  omega

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
