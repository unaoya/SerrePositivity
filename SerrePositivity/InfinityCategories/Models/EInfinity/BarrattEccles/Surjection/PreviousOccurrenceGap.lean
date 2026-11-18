module

public import SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.DeletionSigns
public import Mathlib.Data.List.FinRange

/-!
模型。文献の定義との比較は後で
# 直前の同値の出現と削除位置の間の不出現

概要：Berger–Fresse §1.4.4 の中間行に削除値が現れないことの有限語での根拠を与える。
方針：前の出現集合の最大性から開区間内の同値の出現を排除する。
規約：全射性や非退化性を要求しない。
使われ方：実際の table の中間行に早い除外の輸送を適用する。
-/

@[expose] public section

namespace SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection

/-- 概要：直前の同値の出現と現在位置の間には同じ値がない（BF §1.4.4）。
方針：中間位置が前の出現集合の最大値を超えることに矛盾する。
規約：現在位置が最終出現かどうかは問わない。
使われ方：相殺する二行の間の出力に削除値がないことを示す。 -/
lemma previousOccurrence_no_between {n l : ℕ} (v : Fin l → Fin n) (k : Fin l)
    (hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences v k).Nonempty) (j : Fin l)
    (hj : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences v k).max' hp < j) (hk : j < k) : v j ≠ v k := by
  intro he
  have hm : j ∈ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences v k := by
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hk, he⟩
  have hb := Finset.le_max' (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences v k) j hm
  exact (not_lt_of_ge hb) hj

/-- 概要：直前の出現直後から現在位置直前までのリストに削除値はない（BF §1.4.4）。
方針：drop と take の所属を区間内の有限添字へ戻す。
規約：空の中間区間も含む。
使われ方：中間行の抽出証跡の平坦化に早い除外を適用する。 -/
lemma previousOccurrence_not_mem_slice {n l : ℕ} (v : Fin l → Fin n) (k : Fin l)
    (hp : (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences v k).Nonempty) :
    v k ∉ ((List.ofFn v).drop ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences v k).max' hp).val.succ).take
      (k.val - ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences v k).max' hp).val.succ) := by
  intro hx
  let p := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrences v k).max' hp
  obtain ⟨j, hj, he⟩ := List.mem_take_iff_getElem.mp hx
  have hjlen : j < ((List.ofFn v).drop (p.val + 1)).length := (Nat.lt_min.mp hj).2
  have hjpos : j < k.val - (p.val + 1) := (Nat.lt_min.mp hj).1
  have hk := k.isLt
  let q : Fin l := ⟨p.val + 1 + j, by omega⟩
  have hv : v q = v k := by
    simpa only [List.getElem_drop, List.getElem_ofFn, q] using he
  apply _root_.SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection.previousOccurrence_no_between v k hp q _ _ hv
  · change p.val < p.val + 1 + j
    omega
  · change p.val + 1 + j < k.val
    omega

end SerrePositivity.InfinityCategories.Models.EInfinity.BarrattEccles.Surjection
