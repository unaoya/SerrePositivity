module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ConeTriangleIndex
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ConeWithoutFirst
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedRecoverIndex

/-!
概要：始点／終点を除いた三角形添字像を、元の非零相／非二相の部分集合へ回収する。
方針：元の実 cochain・次数・部分集合と切断の一意性を使う。
規約：残る一項同士の比較は別工程。使われ方：大域評価三角形の混合 HA。
-/
@[expose] public section
namespace SerrePositivity.ComplexLimits

lemma withoutFirst_image_coneTriangleFrontIndex {n : ℕ} (τ : Fin (n + 1) →o Fin 3)
    (I : Finset (Fin (n + 1))) :
    _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst (I.image (_root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex τ)) =
      I.filter (fun i => τ i ≠ 0) := by
  ext x
  simp only [_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.withoutFirst, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_image]
  constructor
  · rintro ⟨i, hi, he⟩
    by_cases hz : τ i = 0
    · rw [_root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex_zero τ i hz] at he
      exact False.elim (Fin.succ_ne_zero x he.symm)
    · rw [_root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex_ne_zero τ i hz] at he
      have hix := Fin.succ_injective _ he
      subst i
      exact ⟨hi, hz⟩
  · rintro ⟨hi, hz⟩
    exact ⟨x, hi, _root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex_ne_zero τ x hz⟩

lemma withoutLast_image_coneTriangleBackIndex {n : ℕ} (τ : Fin (n + 1) →o Fin 3)
    (I : Finset (Fin (n + 1))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast (I.image (_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex τ)) =
      I.filter (fun i => τ i ≠ 2) := by
  ext x
  simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast, Finset.mem_filter,
    Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨i, hi, he⟩
    by_cases ht : τ i = 2
    · rw [_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex_two τ i ht] at he
      exact False.elim (Fin.castSucc_ne_last x he.symm)
    · rw [_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex_ne_two τ i ht] at he
      have hix := Fin.castSucc_injective _ he
      subst i
      exact ⟨hi, ht⟩
  · rintro ⟨hi, ht⟩
    exact ⟨x, hi, _root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex_ne_two τ x ht⟩
end SerrePositivity.ComplexLimits
