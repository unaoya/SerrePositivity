module
public import SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.ShiftUnitValues

/-!
概要：連続する二つの shift 斉次単位の定数符号。
方針：整数三角数の差を計算し、偶数冪を消す。
規約：負の shift を含む全整数で成り立つ。
使われ方：bar の一次列の外側の符号との相殺。
-/
@[expose] public section
namespace SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison

lemma dgBarShiftUnitSign_succ_mul (s : ℤ) :
    _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarShiftUnitSign (s + 1) * _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarShiftUnitSign s = (s + 1).negOnePow := by
  have ht : (s + 1) * (s + 1 - 1) / 2 = s * (s - 1) / 2 + s := by
    have h : (s + 1) * (s + 1 - 1) = s * (s - 1) + 2 * s := by ring
    rw [h, Int.add_mul_ediv_left _ _ (by decide)]
  have h : ((s + 1) * (s + 1) + (s + 1) * (s + 1 - 1) / 2) +
      (s * s + s * (s - 1) / 2) =
    2 * (s * s + s * (s - 1) / 2 + s) + (s + 1) := by
    rw [ht]
    ring
  unfold _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarShiftUnitSign
  rw [← Int.negOnePow_add, h, Int.negOnePow_add, Int.negOnePow_two_mul, one_mul]

lemma dgBarShiftUnitSign_cancel (s : ℤ) :
    s.negOnePow * (_root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarShiftUnitSign s * _root_.SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison.dgBarShiftUnitSign (s - 1)) = 1 := by
  have h := dgBarShiftUnitSign_succ_mul (s - 1)
  rw [sub_add_cancel] at h
  rw [h, ← Int.negOnePow_add, ← two_mul, Int.negOnePow_two_mul]

end SerrePositivity.InfinityCategories.HA.DerivedCategoryModels.CoherentBar.StrictComparison
