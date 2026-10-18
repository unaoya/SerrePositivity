module

public import SerrePositivity.InfinityCategories.DoldKanComparison.AWBoundarySum

/-!
# 切断点と異なる点を削除した AW 項

概要：切断点の左または右で削除した AW 項は、対応する片側成分の削除との合成である。
方針：削除と切断の集合を同定し、削除された側の次数だけを一つ上げる。
規約：切断点そのものの削除はこの二つの式に含めず、別途相殺する。
使われ方：HA 1.3.1.13、Kerodon 2.5.8 の AW の標準方程式の保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.DoldKanComparison

open CategoryTheory DifferentialGraded DGNerve.PinchedHom

variable {R : Type u} [CommRing R] {D : Type v} [DGCategory R D] {x y z : D}

/-- 概要：切断点より左での削除は後の射の接頭成分の次数だけを一つ上げる。
方針：接尾部分は変わらず、接頭部分の濃度だけが一つ減ることを使う。
規約：元の成分の次数は k、削除後の合成の次数は k+1。
使われ方：Kerodon 2.5.8 の左側の削除項の比較。 -/
lemma awTerm_erase_left {n : ℕ} (g : LinearData R y z n) (f : LinearData R x y n)
    (J : Finset (Fin (n + 1))) (i : J) (j : Fin (n + 1)) (hj : j ∈ J) (hji : j < i.val)
    (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    awTerm g f (J.erase j) ⟨i.val, Finset.mem_erase.mpr ⟨ne_of_gt hji, i.property⟩⟩
      (k + 1) (by have := Finset.card_erase_add_one hj; omega) =
        compose R
          (g.component ((J.filter (· ≤ i.val)).erase j)
            (1 - ((J.filter (· ≤ i.val)).card : ℤ) + 1)
            ⟨i.val, Finset.mem_erase.mpr
              ⟨ne_of_gt hji, Finset.mem_filter.mpr ⟨i.property, le_rfl⟩⟩⟩
            (by
              have hc := Finset.card_erase_add_one
                (show j ∈ J.filter (· ≤ i.val) from Finset.mem_filter.mpr ⟨hj, hji.le⟩)
              omega))
          (f.component (J.filter (i.val ≤ ·)) _ (AWIndex.right_nonempty i.property) rfl)
          (by have := AWIndex.degree_add i.property; omega) := by
  have hjl : j ∈ J.filter (· ≤ i.val) := Finset.mem_filter.mpr ⟨hj, hji.le⟩
  unfold awTerm
  apply compose_eq_of_heq
  · exact component_heq_of_eq g _ _ (Finset.filter_erase _ _ _) _ _ _ _ _ _
  · exact component_heq_of_eq f _ _ (AWIndex.erase_right_of_lt hji) _ _ _ _ _ _
  · rw [AWIndex.erase_right_of_lt hji]
  · rw [Finset.filter_erase]
    change 1 - (((J.filter (· ≤ i.val)).erase j).card : ℤ) =
      1 - ((J.filter (· ≤ i.val)).card : ℤ) + 1
    have hc := Finset.card_erase_add_one hjl
    omega

/-- 概要：切断点より右での削除は前の射の接尾成分の次数だけを一つ上げる。
方針：接頭部分は変わらず、接尾部分の濃度だけが一つ減ることを使う。
規約：元の成分の次数は k、削除後の合成の次数は k+1。
使われ方：Kerodon 2.5.8 の右側の削除項の比較。 -/
lemma awTerm_erase_right {n : ℕ} (g : LinearData R y z n) (f : LinearData R x y n)
    (J : Finset (Fin (n + 1))) (i : J) (j : Fin (n + 1)) (hj : j ∈ J) (hij : i.val < j)
    (k : ℤ) (hk : k = 1 - (J.card : ℤ)) :
    awTerm g f (J.erase j) ⟨i.val, Finset.mem_erase.mpr ⟨ne_of_lt hij, i.property⟩⟩
      (k + 1) (by have := Finset.card_erase_add_one hj; omega) =
        compose R
          (g.component (J.filter (· ≤ i.val)) _ (AWIndex.left_nonempty i.property) rfl)
          (f.component ((J.filter (i.val ≤ ·)).erase j)
            (1 - ((J.filter (i.val ≤ ·)).card : ℤ) + 1)
            ⟨i.val, Finset.mem_erase.mpr
              ⟨ne_of_lt hij, Finset.mem_filter.mpr ⟨i.property, le_rfl⟩⟩⟩
            (by
              have hc := Finset.card_erase_add_one
                (show j ∈ J.filter (i.val ≤ ·) from Finset.mem_filter.mpr ⟨hj, hij.le⟩)
              omega))
          (by have := AWIndex.degree_add i.property; omega) := by
  have hjr : j ∈ J.filter (i.val ≤ ·) := Finset.mem_filter.mpr ⟨hj, hij.le⟩
  unfold awTerm
  apply compose_eq_of_heq
  · exact component_heq_of_eq g _ _ (AWIndex.erase_left_of_lt hij) _ _ _ _ _ _
  · exact component_heq_of_eq f _ _ (Finset.filter_erase _ _ _) _ _ _ _ _ _
  · rw [Finset.filter_erase]
    change 1 - (((J.filter (i.val ≤ ·)).erase j).card : ℤ) =
      1 - ((J.filter (i.val ≤ ·)).card : ℤ) + 1
    have hc := Finset.card_erase_add_one hjr
    omega
  · rw [AWIndex.erase_left_of_lt hij]

end SerrePositivity.InfinityCategories.DoldKanComparison
