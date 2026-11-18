module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ConeFirstIndex

/-!
概要：始頂点を含む元の cone 成分から、普遍 cochain の添字集合を回収する。
方針：後続元での所属条件で有限集合を制限し、元の集合と端点を復元する。
規約：元の成分の濃度と最大点を保持する。使われ方：実 cone の混合成分の次数と終点。
-/
@[expose] public section
namespace SerrePositivity.ComplexLimits.ConeHeadIndex


def withoutFirst {n : ℕ} (I : Finset (Fin (n + 2))) : Finset (Fin (n + 1)) :=
  Finset.univ.filter (fun i => i.succ ∈ I)

lemma image_withoutFirst {n : ℕ} (I : Finset (Fin (n + 2))) :
    (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).image Fin.succ = I.erase 0 := by
  ext i
  induction i using Fin.cases with
  | zero => simp
  | succ i => simp [_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst]

lemma withFirst_withoutFirst {n : ℕ} (I : Finset (Fin (n + 2))) (h : 0 ∈ I) :
    _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withFirst (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I) = I := by
  rw [_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withFirst, _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.image_withoutFirst, Finset.insert_erase h]

lemma withoutFirst_withFirst {n : ℕ} (J : Finset (Fin (n + 1))) :
    _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withFirst J) = J := by
  ext j
  simp [_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst, _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withFirst]

lemma card_withoutFirst {n : ℕ} (I : Finset (Fin (n + 2))) (h : 0 ∈ I) :
    I.card = (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).card + 1 := by
  rw [← _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.card_withFirst, _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withFirst_withoutFirst I h]

lemma withoutFirst_nonempty {n : ℕ} {I : Finset (Fin (n + 2))} (hI : 2 ≤ I.card)
    (h : 0 ∈ I) : (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).Nonempty := by
  apply Finset.card_pos.mp
  have := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.card_withoutFirst I h
  omega

lemma max_withoutFirst {n : ℕ} (I : Finset (Fin (n + 2))) (hI : 2 ≤ I.card) (h : 0 ∈ I) :
    ((_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I).max' (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst_nonempty hI h)).succ = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) := by
  have hr := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withFirst_withoutFirst I h
  have he := _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.max_withFirst (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst_nonempty hI h)
    (show (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withFirst (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst I)).Nonempty by rw [hr]; exact _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)
  simpa only [hr] using he

end SerrePositivity.ComplexLimits.ConeHeadIndex
