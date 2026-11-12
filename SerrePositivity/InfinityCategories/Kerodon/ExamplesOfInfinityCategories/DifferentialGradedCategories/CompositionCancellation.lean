module
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.BoundaryDecomposition

/-! # 削除・切断の混合項と三重合成の相殺

概要：削除と切断の二つの順序の係数、および結合律で一致する三重合成の係数を比較する。
方針：右側点数の符号等式と通常順合成の結合律を組み合わせる。
規約：HA Proposition 1.3.1.10。使われ方：主残差恒等式の混合部分と三重合成部分の消去。

対応節は Kerodon 2.5（Tag 00ND）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u v

namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories

open DifferentialGraded

namespace Index

/-- 概要：k より右の j を削除してから k で切断する係数は、右切断後の j 削除の係数の負。
方針：削除順交換の符号と右切断で右側点数が変わらないことを使う。
規約：HA Proposition 1.3.1.10。使われ方：右側の削除・切断の混合項の相殺。 -/
lemma sign_mixed_right {α : Type*} [LinearOrder α] (I : Finset α)
    {j k : α} (hj : j ∈ I) (hk : k ∈ I) (hkj : k < j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j * _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.erase j) k = -(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I k * _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (k ≤ ·)) j) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign_erase_swap I hj hk (ne_of_gt hkj), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign_right_cut I hkj.le]
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.erase k) j = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j := by
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.right_filter_erase_le I hkj.le]
  rw [he]

/-- 概要：右側の削除・切断の二順序の寄与は同じ値に作用すると相殺する。
方針：符号スカラーの積をまとめ、係数の反転を使う。
規約：HA Proposition 1.3.1.10。使われ方：混合項の右側部分の消去。 -/
lemma mixed_right_cancel {α : Type*} [LinearOrder α] {M : Type*} [AddCommGroup M]
    (I : Finset α) {j k : α} (hj : j ∈ I) (hk : k ∈ I) (hkj : k < j) (z : M) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j • (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.erase j) k • z) +
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I k • (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (k ≤ ·)) j • z) = 0 := by
  rw [smul_smul, smul_smul, sign_mixed_right I hj hk hkj]
  simp [Units.smul_def]

/-- 概要：k より左の j の削除と切断の二順序の寄与は、Leibniz の次数符号を含めて相殺する。
方針：左切断での右側点数と全体の右側点数の分割による係数等式を使う。
規約：HA Proposition 1.3.1.10。使われ方：混合項の左側部分の消去。 -/
lemma mixed_left_cancel {α : Type*} [LinearOrder α] {M : Type*} [AddCommGroup M]
    (I : Finset α) {j k : α} (hk : k ∈ I) (hjk : j < k) (z : M) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j • (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.erase j) k • z) +
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I k • ((2 - ((I.filter (k ≤ ·)).card : ℤ)).negOnePow •
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (· ≤ k)) j • z)) = 0 := by
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.erase j) k = _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I k := by
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.right_filter_erase_le I hjk.le]
  rw [he]
  simp only [smul_smul, ← mul_assoc]
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j * _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I k =
      -(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I k * (2 - ((I.filter (k ≤ ·)).card : ℤ)).negOnePow *
        _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (· ≤ k)) j) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign_right_cut I hjk.le] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign_double_cut I hk hjk
  rw [hc]
  simp [Units.smul_def]

/-- 概要：削除後の切断と左右切断後の削除の混合二重和は全体として零になる。
方針：削除点を除く和を条件付きの共通の直積の和に戻し、大小の二場合で係数を相殺する。
規約：HA Proposition 1.3.1.10。使われ方：同じ合成値にそろえた全ての混合項の一括消去。 -/
lemma sum_mixed_cancel {α : Type*} [LinearOrder α] {M : Type*} [AddCommGroup M]
    (I K : Finset α) (hKI : K ⊆ I) (f : α → α → M) :
    (∑ j ∈ K, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j • ∑ k ∈ K.erase j, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.erase j) k • f j k) +
    (∑ k ∈ K, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I k • ∑ j ∈ K.filter (k < ·), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (k ≤ ·)) j • f j k) +
    (∑ k ∈ K, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I k • ((2 - ((I.filter (k ≤ ·)).card : ℤ)).negOnePow •
      ∑ j ∈ K.filter (· < k), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (· ≤ k)) j • f j k)) = 0 := by
  have hErase : ∀ j, K.erase j = K.filter (fun k => j ≠ k) := by
    intro j
    ext k
    simp only [Finset.mem_erase, Finset.mem_filter]
    tauto
  simp only [hErase, Finset.sum_filter, Finset.smul_sum, smul_ite, smul_zero]
  rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro k hk
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j hj
  by_cases h : j = k
  · subst j
    simp
  · rcases lt_or_gt_of_ne h with hlt | hgt
    · simpa only [ite_eq_left (ne_of_lt hlt), ite_eq_right (not_lt_of_ge hlt.le),
        ite_eq_left hlt, zero_add, add_zero] using mixed_left_cancel I (hKI hk) hlt (f j k)
    · simpa only [ite_eq_left (ne_of_gt hgt), ite_eq_left hgt,
        ite_eq_right (not_lt_of_ge hgt.le), zero_add, add_zero] using
        mixed_right_cancel I (hKI hj) (hKI hk) hgt (f j k)

/-- 概要：二重切断の二つの順序の係数を持つ二重和は、Leibniz 符号も含めて相殺する。
方針：内部点の順序付き対の二重和を交換し、各対の係数の反転を使う。
規約：HA Proposition 1.3.1.10。使われ方：結合律で共通の合成値にそろえた三重合成項の消去。 -/
lemma sum_double_cut_cancel {α : Type*} [LinearOrder α] {M : Type*} [AddCommGroup M]
    (I K : Finset α) (hKI : K ⊆ I) (f : α → α → M) :
    (∑ j ∈ K, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j • ∑ k ∈ K.filter (j < ·),
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (j ≤ ·)) k • f j k) +
    (∑ k ∈ K, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I k • ((2 - ((I.filter (k ≤ ·)).card : ℤ)).negOnePow •
      ∑ j ∈ K.filter (· < k), _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (· ≤ k)) j • f j k)) = 0 := by
  simp only [Finset.sum_filter, Finset.smul_sum, smul_ite, smul_zero]
  rw [Finset.sum_comm, ← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro k hk
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_eq_zero
  intro j _
  by_cases hjk : j < k
  · simp only [ite_eq_left hjk, smul_smul, ← mul_assoc]
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign_double_cut I (hKI hk) hjk]
    simp [Units.smul_def]
  · simp only [ite_eq_right hjk, add_zero]

end Index

variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D]

/-- 概要：結合律で一致する三重合成の二つの寄与は、切断の符号と Leibniz 符号により相殺する。
方針：通常順合成の結合律で共通の射にそろえ、二重切断の係数の反転を使う。
規約：HA Proposition 1.3.1.10。使われ方：残差恒等式で残る三重合成項の相殺。 -/
lemma cubic_compose_cancel {α : Type*} [LinearOrder α] (I : Finset α)
    {j k : α} (hk : k ∈ I) (hjk : j < k)
    {w x y z : D} {p q r m : ℤ}
    (f : GradedHom A w x p) (g : GradedHom A x y q) (h : GradedHom A y z r)
    (hr : r = 2 - ((I.filter (k ≤ ·)).card : ℤ)) (hm : p + q + r = m) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j • (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (j ≤ ·)) k •
      compose A (compose A h g rfl) f (by omega)) +
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I k • (r.negOnePow • (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (· ≤ k)) j •
      compose A h (compose A g f rfl) hm)) = 0 := by
  rw [← compose_assoc A f g h hm]
  simp only [smul_smul, ← mul_assoc]
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I j * _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (j ≤ ·)) k =
      -(_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign I k * r.negOnePow * _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign (I.filter (· ≤ k)) j) := by
    simpa only [hr] using _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.sign_double_cut I hk hjk
  rw [hc]
  simp [Units.smul_def]

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories
