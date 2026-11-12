module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedHornFilling

/-! 指定した最上位の微分を持つ削除和と、一般の最上位方程式からの欠面の回収。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded

lemma dgGluingDeletionSum_target {α V : Type*} [LinearOrder α] [AddCommGroup V]
    (J : Finset α) (i : α) (hi : i ∈ J) (f : α → V) (z : V)
    (hf : f i = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deletionSolution J i f + (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deletionSign J i)⁻¹ • z) :
    (∑ j ∈ J, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deletionSign J j • f j) = z := by
  rw [← Finset.add_sum_erase J _ hi, hf]
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deletionSolution, smul_add, smul_neg, smul_smul,
    mul_inv_cancel, one_smul]
  abel

variable {R : Type u} [CommRing R] {D : Type v} [_root_.SerrePositivity.DifferentialGraded.DGCategory R D] {x y : D}

lemma dgGluingPinched_missing_equation {n : ℕ} (f : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData R x y n)
    (J : Finset (Fin (n + 1))) (k : ℤ) (hJ : 2 ≤ J.card)
    (hk : k = 1 - (J.card : ℤ)) (i : Fin (n + 1)) (hi : i ∈ J)
    (htop : _root_.SerrePositivity.DifferentialGraded.differential R (f.component J k (Finset.card_pos.mp (by omega)) hk) =
      f.rhs J k hk)
    (hother : ∀ j : J, j.val ≠ i → f.residual (J.erase j.val) (k + 1)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.erase_nonempty hJ j.val j.property)
      (by have := Finset.card_erase_add_one j.property; omega) = 0) :
    _root_.SerrePositivity.DifferentialGraded.differential R (f.component (J.erase i) (k + 1) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.erase_nonempty hJ i hi)
      (by have := Finset.card_erase_add_one hi; omega)) =
      f.rhs (J.erase i) (k + 1) (by have := Finset.card_erase_add_one hi; omega) := by
  have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.differential_rhs_residual f J k hJ hk
  have hzero : _root_.SerrePositivity.DifferentialGraded.differential R (f.rhs J k hk) = 0 := by
    rw [← htop]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.differential_squared _
  rw [Finset.sum_eq_single (⟨i, hi⟩ : J)] at hs
  · have he := congrArg (fun t => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.deletionSign J i)⁻¹ • t) (hs.symm.trans hzero)
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.residual_eq_zero_iff f (J.erase i) (k + 1)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LinearData.erase_nonempty hJ i hi)
      (by have := Finset.card_erase_add_one hi; omega)).mp
    simpa only [smul_smul, inv_mul_cancel, one_smul, smul_zero] using he
  · intro j _ hji
    rw [hother j (fun he => hji (Subtype.ext he)), smul_zero]
  · intro hnot
    exact False.elim (hnot (Finset.mem_univ _))

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
