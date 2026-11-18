module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ConeFirstBoundary
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedLinear

/-!
概要：実 cone の混合方程式で、内部削除和へ最後の一項を戻す有限和を計算する。
方針：後続元で再添字付けし、終端項の係数一と符号積を使う。
規約：元の全有限和を保つ。使われ方：元の線形微分方程式の右辺の回収。
-/
@[expose] public section
noncomputable section
namespace SerrePositivity.ComplexLimits.ConeHeadIndex

lemma signed_coefficient_commute {M : Type*} [AddCommGroup M] (k g : ℤ) (v : M) :
    g.negOnePow • ((k + 1).negOnePow • v) =
      k.negOnePow • ((g + 1).negOnePow • v) := by
  simp only [Int.negOnePow_add, smul_smul]
  congr 1
  ac_rfl

lemma sum_restore_terminal {n : ℕ} {M : Type*} [AddCommGroup M]
    (J : Finset (Fin (n + 1))) (hm : Fin.last n ∈ J)
    (f : J → M) (r : ℤˣ) :
    (∑ j : J, if j.val < Fin.last n then _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign J j.val • (r • f j) else 0) +
      r • f ⟨Fin.last n, hm⟩ = ∑ j : J, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign J j.val • (r • f j) := by
  let b : J := ⟨Fin.last n, hm⟩
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign J b.val = 1 := by
    unfold _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign
    have he : J.filter (b.val < ·) = ∅ := by
      ext i
      simp only [Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
      intro _
      exact not_lt_of_ge (Fin.le_last i)
    rw [he]
    rfl
  have hsum : (∑ j : J, if j = b then 0 else _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign J j.val • (r • f j)) +
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign J b.val • (r • f b) = ∑ j : J, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign J j.val • (r • f j) := by
    calc
      _ = (∑ j : J, if j = b then 0 else _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign J j.val • (r • f j)) +
          (∑ j : J, if j = b then _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign J b.val • (r • f b) else 0) := by simp
      _ = ∑ j : J, ((if j = b then 0 else _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign J j.val • (r • f j)) +
          (if j = b then _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign J b.val • (r • f b) else 0)) :=
        Finset.sum_add_distrib.symm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        by_cases he : j = b <;> simp [he]
  have he : ∀ j : J,
      (if j.val < Fin.last n then _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign J j.val • (r • f j) else 0) =
        (if j = b then 0 else _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign J j.val • (r • f j)) := by
    intro j
    by_cases hj : j = b
    · subst j
      simp [b]
    · have hlt : j.val < Fin.last n := lt_of_le_of_ne (Fin.le_last j.val)
        (fun he => hj (Subtype.ext he))
      simp [hj, hlt]
  simp_rw [he]
  simpa only [hb, one_smul] using hsum

lemma sum_interior_zero_last {n : ℕ} {M : Type*} [AddCommMonoid M]
    (I : Finset (Fin (n + 2))) (f : Fin (n + 2) → M) :
    (∑ j ∈ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.interior I 0 (Fin.last (n + 1)), f j) =
      ∑ j : _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I,
        if j.val < Fin.last n then f j.val.succ else 0 := by
  rw [_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.interior_zero_last]
  rw [Finset.sum_image (fun i _ j _ h => Fin.succ_injective _ h)]
  have he : (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).erase (Fin.last n) =
      (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).filter (· < Fin.last n) := by
    ext i
    simp [lt_iff_le_and_ne, Fin.le_last, and_comm]
  rw [he, Finset.sum_filter, ← Finset.sum_coe_sort]

lemma sum_restore_terminal_linear {n : ℕ} {M : Type*} [AddCommGroup M]
    (J : Finset (Fin (n + 1))) (hm : Fin.last n ∈ J) (f : J → M) (k : ℤ) :
    (∑ j : J, if j.val < Fin.last n then
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign J j.val • ((k + 1).negOnePow • f j) else 0) +
      (k + 1).negOnePow • f ⟨Fin.last n, hm⟩ =
        k.negOnePow • ∑ j : J,
          (((J.filter (j.val < ·)).card : ℤ) + 1).negOnePow • f j := by
  rw [_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.sum_restore_terminal, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  exact _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.signed_coefficient_commute k _ (f j)

end SerrePositivity.ComplexLimits.ConeHeadIndex
