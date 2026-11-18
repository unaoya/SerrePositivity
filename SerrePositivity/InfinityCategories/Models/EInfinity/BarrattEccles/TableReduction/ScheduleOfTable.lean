module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Sequence
public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.SuccessfulRowBounds
public import Mathlib.Data.List.GetD

/-!
模型。文献の定義との比較は後で
# 正しい行列・行長総和を持つ成功表から Schedule を復元

概要：Berger–Fresse §1.5.8 の復元表の実際の行長を元の次数の Schedule に包む。
方針：元の逆置換行列との一致で有限添字と arity 上界を固定し、実際の総和を移す。
規約：行列と行長総和以外は実際の抽出成功から得る。
使われ方：圧縮外側表を元の外側 TR の本来の Schedule として使う。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction

/-- 概要：元の行列と総和を持つ成功表は実際の元の次数の Schedule で表示できる（BF §1.5.8）。
方針：復元表の各行長を getD で取り、成功の上下界と元の総和をそのまま使う。
規約：返す Schedule の rows は元の表リストと厳密に一致する。
使われ方：元の外側成功表と元の次数の TR 項を逆構成する。 -/
lemma schedule_of_table {n d : ℕ} (w : Fin (d + 1) → Equiv.Perm (Fin n))
    (table : List (List (Fin n) × ℕ)) (out : List (Fin n))
    (h : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows table [] = some out)
    (hmatrix : table.map Prod.fst = List.ofFn (fun i => List.ofFn (w i).symm))
    (hsum : (table.map Prod.snd).sum = n + d) :
    ∃ r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r = table := by
  have hlen : table.length = d + 1 := by
    simpa only [List.length_map, List.length_ofFn] using congrArg List.length hmatrix
  have hindex (i : Fin (d + 1)) : i.val < table.length := by rw [hlen]; exact i.isLt
  have hrow (i : Fin (d + 1)) : (table.getD i.val ([], 0)).1 = List.ofFn (w i).symm := by
    have he := congrArg (fun xs : List (List (Fin n)) => xs[i.val]?) hmatrix
    rw [List.getElem?_eq_getElem (by simpa only [List.length_map] using hindex i),
      List.getElem_map, List.getElem?_ofFn, dite_eq_left i.isLt] at he
    rw [List.getD_eq_getElem table ([], 0) (hindex i)]
    exact Option.some.inj he
  have hbounds := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.reduceRows_row_bounds table [] out h
  have hweight (i : Fin (d + 1)) :
      0 < (table.getD i.val ([], 0)).2 ∧ (table.getD i.val ([], 0)).2 ≤ n := by
    have hm : table.getD i.val ([], 0) ∈ table := by
      rw [List.getD_eq_getElem table ([], 0) (hindex i)]
      exact List.getElem_mem (hindex i)
    have hb := hbounds _ hm
    rw [hrow i, List.length_ofFn] at hb
    exact hb
  let weights : Fin (d + 1) → Fin (n + 1) := fun i =>
    ⟨(table.getD i.val ([], 0)).2, by have hb := (hweight i).2; omega⟩
  have hweights : List.ofFn (fun i : Fin (d + 1) => (table.getD i.val ([], 0)).2) =
      table.map Prod.snd := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_map, hlen]
    · intro i hi hj
      have ht : i < table.length := by simpa only [List.length_map] using hj
      simp only [List.getElem_ofFn, List.getElem_map, List.getD_eq_getElem table ([], 0) ht]
  have hpositive (i : Fin (d + 1)) : 0 < (weights i).val := (hweight i).1
  have htotal : (∑ i, (weights i).val) = n + d := by
    change (∑ i : Fin (d + 1), (table.getD i.val ([], 0)).2) = n + d
    rw [← List.sum_ofFn, hweights]
    exact hsum
  let r : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.Schedule n d := ⟨weights, hpositive, htotal⟩
  refine ⟨r, ?_⟩
  have hdata : List.ofFn (fun i : Fin (d + 1) => table.getD i.val ([], 0)) = table := by
    apply List.ext_getElem
    · simp only [List.length_ofFn, hlen]
    · intro i hi hj
      simp only [List.getElem_ofFn, List.getD_eq_getElem table ([], 0) hj]
  calc
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction.rows w r = List.ofFn (fun i : Fin (d + 1) => table.getD i.val ([], 0)) := by
      apply congrArg List.ofFn
      funext i
      apply Prod.ext
      · exact (hrow i).symm
      · rfl
    _ = table := hdata

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.TableReduction
