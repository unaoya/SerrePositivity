module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index

/-!
概要：実 cone の始頂点を含む成分を、残りの有限集合へ移す添字を定義する。
方針：後続元の像に零頂点を加え、濃度・最小点・最大点を計算する。
規約：元の有限集合と順序を保持する。使われ方：元の普遍 cochain の実 cone 成分。
-/
@[expose] public section
namespace SerrePositivity.EInfinity.ComplexLimits.ConeHeadIndex


def withFirst {n : ℕ} (J : Finset (Fin (n + 1))) : Finset (Fin (n + 2)) :=
  insert 0 (J.image Fin.succ)

lemma zero_not_mem_image {n : ℕ} (J : Finset (Fin (n + 1))) :
    (0 : Fin (n + 2)) ∉ J.image Fin.succ := by simp

lemma card_withFirst {n : ℕ} (J : Finset (Fin (n + 1))) :
    (withFirst J).card = J.card + 1 := by
  rw [withFirst, Finset.card_insert_of_notMem (zero_not_mem_image J),
    Finset.card_image_of_injective _ (Fin.succ_injective _)]

lemma min_withFirst {n : ℕ} (J : Finset (Fin (n + 1))) (h : (withFirst J).Nonempty) :
    (withFirst J).min' h = 0 := by
  apply (Finset.isLeast_min' _ h).unique
  exact ⟨Finset.mem_insert_self _ _, fun _ _ => Fin.zero_le _⟩

lemma max_withFirst {n : ℕ} {J : Finset (Fin (n + 1))} (hJ : J.Nonempty)
    (h : (withFirst J).Nonempty) : (J.max' hJ).succ = (withFirst J).max' h := by
  symm
  apply (Finset.isGreatest_max' _ h).unique
  refine ⟨Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨_, J.max'_mem hJ, rfl⟩), ?_⟩
  intro j hj
  rcases Finset.mem_insert.mp hj with hz | hj
  · subst j
    exact Fin.zero_le _
  · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hj
    exact Fin.succ_le_succ_iff.mpr ((J.isGreatest_max' hJ).2 hi)

end SerrePositivity.EInfinity.ComplexLimits.ConeHeadIndex
