module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ConePenultimateCuts
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.LinearBoundary

/-!
概要：実 cone の内部削除と最後の切断の添字を、元の普遍 cochain の添字へ移す。
方針：後続元による所属判定と最後の切断の左集合の式を使う。
規約：同じ有限集合と削除符号を保つ。使われ方：混合 HA の全線形有限和の比較。
-/
@[expose] public section
namespace SerrePositivity.ComplexLimits.ConeHeadIndex


lemma filter_above_succ {n : ℕ} (I : Finset (Fin (n + 2))) (j : Fin (n + 1)) :
    I.filter (j.succ < ·) = ((_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).filter (j < ·)).image Fin.succ := by
  ext i
  induction i using Fin.cases with
  | zero => simp
  | succ i => simp [_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst]

lemma sign_succ {n : ℕ} (I : Finset (Fin (n + 2))) (j : Fin (n + 1)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j.succ = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I) j := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign, _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.filter_above_succ,
    Finset.card_image_of_injective _ (Fin.succ_injective _)]
  rfl

lemma interior_zero_last {n : ℕ} (I : Finset (Fin (n + 2))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I 0 (Fin.last (n + 1)) =
      ((_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).erase (Fin.last n)).image Fin.succ := by
  ext i
  induction i using Fin.cases with
  | zero => simp [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior]
  | succ i =>
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior, Finset.mem_filter, Finset.mem_image, Finset.mem_erase,
      _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst, Finset.mem_univ, true_and, Fin.succ_inj,
      exists_eq_right, Fin.succ_pos, true_and]
    constructor
    · intro hi
      exact ⟨(by intro he; subst i; exact (lt_irrefl _ hi.2)), hi.1⟩
    · intro hi
      exact ⟨hi.2, Fin.succ_lt_succ_iff.mpr
        (lt_of_le_of_ne (Fin.le_last i) hi.1)⟩

lemma withoutFirst_left_penultimate_last {n : ℕ} (I : Finset (Fin (n + 2)))
    (hI : 2 ≤ I.card) (hm : I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) = Fin.last (n + 1)) :
    _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst (I.filter (· ≤ _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI)) =
      (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).erase (Fin.last n) := by
  rw [_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.left_filter_penultimate, hm]
  exact _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst_erase_succ I (Fin.last n)

end SerrePositivity.ComplexLimits.ConeHeadIndex
