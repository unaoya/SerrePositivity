module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index
public import Mathlib.Data.Fin.Rev
/-!
概要：dg 反対圏の nerve と単体的反対圏の比較に使う、実成分添字の反転。
方針：Fin.rev の有限集合像により、端点・削除・左右切断を同時に反転する。
規約：次数は同じ濃度から決まる。使われ方：β5 の反変 Hom の模型照合。
-/
@[expose] public section
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
namespace DGNerveOppositeIndex
variable {n : ℕ}
/-- 成分の実頂点集合を順序反転する。 -/
def reverse (I : Finset (Fin (n + 1))) : Finset (Fin (n + 1)) := I.image Fin.rev
@[simp] lemma mem_reverse (I : Finset (Fin (n + 1))) (j : Fin (n + 1)) :
    j ∈ reverse I ↔ j.rev ∈ I := by
  simp only [reverse, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, rfl⟩
    simpa using hi
  · intro h
    exact ⟨j.rev, h, Fin.rev_rev j⟩
@[simp] lemma reverse_reverse (I : Finset (Fin (n + 1))) : reverse (reverse I) = I := by
  ext j
  simp
@[simp] lemma card_reverse (I : Finset (Fin (n + 1))) : (reverse I).card = I.card :=
  Finset.card_image_of_injective I Fin.rev_injective
/-- 反転後も同じ成分次数を使える。 -/
lemma two_le_card_reverse {I : Finset (Fin (n + 1))} (hI : 2 ≤ I.card) :
    2 ≤ (reverse I).card := by simpa using hI
/-- 反転は元の最大端点を最小端点へ送る。 -/
lemma reverse_isLeast {I : Finset (Fin (n + 1))} {b : Fin (n + 1)}
    (hb : IsGreatest (I : Set (Fin (n + 1))) b) :
    IsLeast (reverse I : Set (Fin (n + 1))) b.rev := by
  refine ⟨by simpa using hb.1, ?_⟩
  intro i hi
  have h := hb.2 ((mem_reverse I i).mp hi)
  simpa only [Fin.rev_rev] using (Fin.rev_le_rev).mpr h
/-- 反転は元の最小端点を最大端点へ送る。 -/
lemma reverse_isGreatest {I : Finset (Fin (n + 1))} {a : Fin (n + 1)}
    (ha : IsLeast (I : Set (Fin (n + 1))) a) :
    IsGreatest (reverse I : Set (Fin (n + 1))) a.rev := by
  refine ⟨by simpa using ha.1, ?_⟩
  intro i hi
  have h := ha.2 ((mem_reverse I i).mp hi)
  simpa only [Fin.rev_rev] using (Fin.rev_le_rev).mpr h
/-- 反転した実集合の最小端点を、元の最大端点から厳密に読む。 -/
lemma reverse_min {I : Finset (Fin (n + 1))} (hI : 2 ≤ I.card)
    {b : Fin (n + 1)} (hb : b = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) :
    b.rev = (reverse I).min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty (two_le_card_reverse hI)) := by
  have hg : IsGreatest (I : Set (Fin (n + 1))) b := by
    rw [hb]
    exact I.isGreatest_max' _
  exact (reverse_isLeast hg).unique ((reverse I).isLeast_min' _)
/-- 反転した実集合の最大端点を、元の最小端点から厳密に読む。 -/
lemma reverse_max {I : Finset (Fin (n + 1))} (hI : 2 ≤ I.card)
    {a : Fin (n + 1)} (ha : a = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) :
    a.rev = (reverse I).max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty (two_le_card_reverse hI)) := by
  have hl : IsLeast (I : Set (Fin (n + 1))) a := by
    rw [ha]
    exact I.isLeast_min' _
  exact (reverse_isGreatest hl).unique ((reverse I).isGreatest_max' _)
/-- 内部点の削除と頂点反転は可換。 -/
lemma reverse_erase (I : Finset (Fin (n + 1))) (j : Fin (n + 1)) :
    reverse (I.erase j) = (reverse I).erase j.rev := by
  ext i
  simp only [mem_reverse, Finset.mem_erase]
  simp only [Fin.rev_ne_iff]
/-- 左切断は反転後の右切断になる。 -/
lemma reverse_left (I : Finset (Fin (n + 1))) (j : Fin (n + 1)) :
    reverse (I.filter (· ≤ j)) = (reverse I).filter (j.rev ≤ ·) := by
  ext i
  simp only [mem_reverse, Finset.mem_filter]
  rw [← Fin.rev_le_rev, Fin.rev_rev]
/-- 右切断は反転後の左切断になる。 -/
lemma reverse_right (I : Finset (Fin (n + 1))) (j : Fin (n + 1)) :
    reverse (I.filter (j ≤ ·)) = (reverse I).filter (· ≤ j.rev) := by
  ext i
  simp only [mem_reverse, Finset.mem_filter]
  rw [← Fin.rev_le_rev, Fin.rev_rev]
/-- HA 微分式の符号を決める右側の点集合は、反転後の左側の点集合。 -/
lemma reverse_strictRight (I : Finset (Fin (n + 1))) (j : Fin (n + 1)) :
    reverse (I.filter (j < ·)) = (reverse I).filter (· < j.rev) := by
  ext i
  simp only [mem_reverse, Finset.mem_filter]
  rw [← Fin.rev_lt_rev, Fin.rev_rev]
end DGNerveOppositeIndex
end SerrePositivity.InfinityCategories.Project.DerivedCategories
