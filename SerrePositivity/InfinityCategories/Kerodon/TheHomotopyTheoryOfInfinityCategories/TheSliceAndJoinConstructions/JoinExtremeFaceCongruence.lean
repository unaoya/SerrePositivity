module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.JoinExtremeFaces

/-!
概要：異なる次数の join の単体の両端の面における因子の比較。
方針：対応する区間の頂点数と制限の順序写像を比較し、補った単体の移送を使う。
規約：因子の等式は HEq、頂点数の等式は自然数の等式で明示する。
使われ方：Kerodon Proposition 4.3.3.24（Tag 02QU）、join の内ホーンの充填。

対応節は Kerodon 4.3（Tag 015M）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 概要：左の因子と切断が一致すれば、次数が一つ違っても最初の面の左因子は一致する。
方針：最初の頂点を除く制限の値が一つずれることを比較する。
規約：切断は正。
使われ方：Kerodon Proposition 4.3.3.24（Tag 02QU）、両端の面から充填単体を作る左因子の計算。 -/
lemma Join.delta_zero_left_heq_of_left_heq {X Y : SSet.{u}} {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex X Y (n + 2)) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex X Y (n + 1))
    (hc : s.1.val = t.1.val) (hs : 0 < s.1.val) (hx : HEq s.2.1 t.2.1) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ (0 : Fin (n + 3))).toOrderHom s).2.1
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom t).2.1 := by
  let α := (SimplexCategory.δ (0 : Fin (n + 3))).toOrderHom
  let β := (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom
  have hs' := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.pullCut_delta_zero (n + 1) s.1.val hs (by have := s.1.isLt; omega)
  have ht' := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.pullCut_delta_zero n t.1.val (by omega) (by have := t.1.isLt; omega)
  have hm : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α s.1.val = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut β t.1.val := by
    change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (SimplexCategory.δ (0 : Fin (n + 3))).toOrderHom s.1.val =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut (SimplexCategory.δ (0 : Fin (n + 2))).toOrderHom t.1.val
    omega
  have hα : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α s.1.val ≤ n + 2 := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le _ _
  have hβ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut β t.1.val ≤ n + 1 := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut_le _ _
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap_congr X hm hc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMap α s.1.val) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.leftMap β t.1.val)
    (fun i j hij ↦ by
      change ((0 : Fin (n + 3)).succAbove ⟨i.val, by have := i.isLt; omega⟩).val =
        ((0 : Fin (n + 2)).succAbove ⟨j.val, by have := j.isLt; omega⟩).val
      rw [Fin.succAbove_zero, Fin.succAbove_zero]
      change i.val + 1 = j.val + 1
      omega) s.2.1 t.2.1 (eq_of_heq ((cast_heq _ _).trans hx))
  exact (cast_heq _ _).symm.trans (heq_of_eq he)

/-- 概要：右因子の頂点数と単体が一致すれば、最後の面の右因子も一致する。
方針：最後以外の右側の頂点は値が変わらないことを比較する。
規約：右の因子は空でなく、次数の差は一。
使われ方：Kerodon Proposition 4.3.3.24（Tag 02QU）、両端の面から充填単体を作る右因子の計算。 -/
lemma Join.delta_last_right_heq_of_right_heq {X Y : SSet.{u}} {n : ℕ}
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex X Y (n + 2)) (t : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.Simplex X Y (n + 1))
    (hc : n + 3 - s.1.val = n + 2 - t.1.val)
    (hs : s.1.val ≤ n + 2) (ht : t.1.val ≤ n + 1) (hy : HEq s.2.2 t.2.2) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ (Fin.last (n + 2))).toOrderHom s).2.2
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.simplexMap X Y (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom t).2.2 := by
  let α := (SimplexCategory.δ (Fin.last (n + 2))).toOrderHom
  let β := (SimplexCategory.δ (Fin.last (n + 1))).toOrderHom
  have hs' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α s.1.val = s.1.val := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.pullCut_delta_last (n + 1) s.1.val hs
  have ht' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut β t.1.val = t.1.val := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.Join.pullCut_delta_last n t.1.val ht
  have hm : n + 2 - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α s.1.val = n + 1 - _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut β t.1.val := by omega
  have he := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.augMap_congr Y hm hc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap α s.1.val) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.rightMap β t.1.val)
    (fun i j hij ↦ by
      change ((Fin.last (n + 2)).succAbove ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α s.1.val + i.val, by have := i.isLt; omega⟩).val - s.1.val =
        ((Fin.last (n + 1)).succAbove ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut β t.1.val + j.val, by have := j.isLt; omega⟩).val - t.1.val
      rw [Fin.succAbove_last, Fin.succAbove_last]
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut α s.1.val + i.val - s.1.val = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join.pullCut β t.1.val + j.val - t.1.val
      omega) s.2.2 t.2.2 (eq_of_heq ((cast_heq _ _).trans hy))
  exact (cast_heq _ _).symm.trans (heq_of_eq he)

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
