module
public import SerrePositivity.KST.SConstruction.SimplexHADecodeSubset
public import Mathlib.Order.Hom.Set

/-! # 元の部分集合による HA 頂点列の一意性
概要：同じ終点を加えて元の部分集合が一致する二つの昇順列は、次元も列も一致する。
方針：元の濃度で次元を判定し、同じ終点を除いた有限像で昇順列を判定する。
規約：元の全頂点番号と終点を保持。使われ方：全区間と挿入・削除列の回収式の移送。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction

/-- 元の同じ終点を加えて同じ部分集合を作る昇順列は、同じ次元・同じ列を持つ。 -/
lemma simplexHAColumn_eq_of_subset_eq {N m n : ℕ}
    (v : Fin (m + 1) ↪o Fin (N + 1)) (w : Fin (n + 1) ↪o Fin (N + 1))
    (b : Fin (N + 1)) (hv : v (Fin.last m) < b) (hw : w (Fin.last n) < b)
    (h : simplexHADecodeSubset m v {b} = simplexHADecodeSubset n w {b}) :
    m = n ∧ HEq v w := by
  have hm := simplexHADecodeSubset_card m v {b}
    (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hv)
  have hn := simplexHADecodeSubset_card n w {b}
    (fun _ ht => (Finset.mem_singleton.mp ht) ▸ hw)
  have hc := congrArg Finset.card h
  rw [hm, hn] at hc
  have hmn : m = n := by omega
  refine ⟨hmn, ?_⟩
  subst n
  apply heq_of_eq
  apply OrderEmbedding.eq_of_range_eq
  ext x
  have hmem := Finset.ext_iff.mp h x
  rw [simplexHADecodeSubset_mem, simplexHADecodeSubset_mem] at hmem
  simp only [Finset.mem_singleton] at hmem
  by_cases hxb : x = b
  · subst x
    constructor
    · rintro ⟨j, hj⟩
      exact False.elim ((ne_of_lt ((v.monotone (Fin.le_last j)).trans_lt hv)) hj)
    · rintro ⟨j, hj⟩
      exact False.elim ((ne_of_lt ((w.monotone (Fin.le_last j)).trans_lt hw)) hj)
  · simpa only [Set.mem_range, hxb, or_false] using hmem

end SerrePositivity.KST.SConstruction
