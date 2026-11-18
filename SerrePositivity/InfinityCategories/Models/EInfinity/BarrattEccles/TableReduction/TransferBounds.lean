module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.ScheduleTransfer
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SingletonInsertion
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
模型。文献の定義との比較は後で
# 削除対の行長移動に必要な arity の余裕

概要：Berger–Fresse §1.4.4 の相殺相手の行長が arity の上界を満たすことを導く。
方針：全行の長さ−1 の総和が n−1 であることから二行の上界を得る。
規約：減らす行は長さ 2 以上で、増やす行とは異なる。
使われ方：増やす行の余裕を追加仮定せず、実際の Schedule の移動を作る。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：Schedule の全行の長さ−1 の和に 1 を足すと arity（BF §1.4.4）。
方針：各行の正値性から引いた 1 を足し戻し、行数と総和を代入する。
規約：Schedule が存在すれば arity は正となる。
使われ方：二つの指定行の長さの余裕を計数する。 -/
lemma schedule_excess_sum {n d : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) :
    (∑ i, ((r.val i).val - 1)) + 1 = n := by
  have hp : ∀ x ∈ List.ofFn (fun j => (r.val j).val), 0 < x := by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact r.property.1 i
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.sum_sub_one_add_length (List.ofFn (fun j => (r.val j).val)) hp
  simp only [List.map_ofFn, List.sum_ofFn, List.length_ofFn, Function.comp_apply] at hs
  rw [r.property.2] at hs
  omega

/-- 概要：別の行から長さを一つ減らせるなら受け取り側には arity の余裕がある（BF §1.4.4）。
方針：二行の長さ−1 の和を全体の和で抑える。
規約：二行の相違と減らす行の長さだけを要求する。
使われ方：相殺相手の Schedule の有限添字を無条件に構成する。 -/
lemma schedule_receiver_lt {n d : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d) (donor receiver : Fin (d + 1))
    (hne : donor ≠ receiver) (hd : 1 < (r.val donor).val) : (r.val receiver).val < n := by
  have hs := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.schedule_excess_sum r
  have hp := r.property.1 receiver
  have hsub : ({donor, receiver} : Finset (Fin (d + 1))) ⊆ Finset.univ := by simp
  have hb := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun i => (r.val i).val - 1) (by intro i _ _; omega)
  rw [Finset.sum_pair hne] at hb
  omega

/-- 概要：減らす行の余裕だけから相殺相手の Schedule を構成（BF §1.4.4）。
方針：受け取り側の厳密上界を全体の行長の計数から供給する。
規約：出力の一致や相殺そのものは別に証明する。
使われ方：最終出現削除と行末削除を対応させる実際の行長変更。 -/
def deletionScheduleTransfer {n d : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    (donor receiver : Fin (d + 1)) (hne : donor ≠ receiver)
    (hd : 1 < (r.val donor).val) : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d :=
  _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.scheduleTransfer r donor receiver hne hd (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.schedule_receiver_lt r donor receiver hne hd)

/-- 概要：相殺候補で増やす行の長さは元の長さ＋1（BF §1.4.4）。
方針：自然数の行長の移動の評価式を使う。
規約：Schedule の証明項に依存しない。
使われ方：逆の行長移動の正値性を与える。 -/
@[simp] lemma deletionScheduleTransfer_receiver {n d : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    (i j : Fin (d + 1)) (hne : i ≠ j) (hi : 1 < (r.val i).val) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r i j hne hi).val j).val = (r.val j).val + 1 := by
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit_receiver _ i j

/-- 概要：相殺候補で減らす行の長さは元の長さ−1（BF §1.4.4）。
方針：自然数の行長の移動の評価式を使う。
規約：二行は異なる。
使われ方：削除後の table の長さと逆対応を比較する。 -/
@[simp] lemma deletionScheduleTransfer_donor {n d : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    (i j : Fin (d + 1)) (hne : i ≠ j) (hi : 1 < (r.val i).val) :
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r i j hne hi).val i).val = (r.val i).val - 1 := by
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit_donor _ i j hne

/-- 概要：相殺候補の二行を逆に移すと元の Schedule（BF §1.4.4）。
方針：自然数値の移動の逆を全成分で検証する。
規約：逆操作の長さの余裕は元の正値性から導く。
使われ方：相殺対の行長変更に余分な選択や上界仮定がないことを保証する。 -/
lemma deletionScheduleTransfer_inverse {n d : ℕ} (r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d)
    (i j : Fin (d + 1)) (hne : i ≠ j) (hi : 1 < (r.val i).val) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer r i j hne hi) j i hne.symm
      (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.deletionScheduleTransfer_receiver]; have := r.property.1 j; omega) = r := by
  apply Subtype.ext
  funext k
  apply Fin.ext
  exact congrFun (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.transferUnit_inverse (fun k => (r.val k).val) i j hne (by omega)) k

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
