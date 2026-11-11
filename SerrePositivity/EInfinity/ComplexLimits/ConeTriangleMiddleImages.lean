module
public import SerrePositivity.EInfinity.ComplexLimits.ConeTrianglePrincipalInjectivity
public import SerrePositivity.EInfinity.ComplexLimits.ConeTriangleImage

/-!
概要：元の二つの切断 cochain から回収する集合は、同じ中央相の部分集合である。
方針：元の部分集合・全添字像・実評価射と端点の等式輸送を保持する。
規約：二つの主切断の非零成分比較は別工程。使われ方：大域評価三角形の混合 HA。
-/
@[expose] public section
namespace SerrePositivity.EInfinity.ComplexLimits


lemma withoutFirst_image_penultimate_middle {n : ℕ} (τ : Fin (n + 1) →o Fin 3)
    (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (hp1 : τ (ConeHeadIndex.penultimate I hI) = 1)
    (hbt : τ (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) = 2) :
    ConeHeadIndex.withoutFirst
      ((I.filter (· ≤ ConeHeadIndex.penultimate I hI)).image (coneTriangleFrontIndex τ)) =
      I.filter (fun i => τ i = 1) := by
  rw [withoutFirst_image_coneTriangleFrontIndex]
  ext i
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hi, hip⟩, hz⟩
    have ht := τ.monotone hip
    rw [hp1] at ht
    exact ⟨hi, by omega⟩
  · rintro ⟨hi, hi1⟩
    have hne : i ≠ I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) := by
      intro he
      have ht := congrArg τ he
      rw [hi1, hbt] at ht
      exact (by decide : (1 : Fin 3) ≠ 2) ht
    exact ⟨⟨hi, (I.erase (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))).le_max' i
      (Finset.mem_erase.mpr ⟨hne, hi⟩)⟩, by rw [hi1]; decide⟩

lemma withoutLast_image_second_middle {n : ℕ} (τ : Fin (n + 1) →o Fin 3)
    (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (hs1 : τ (ConeHeadIndex.second I hI) = 1)
    (haz : τ (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) = 0) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.withoutLast
      ((I.filter (ConeHeadIndex.second I hI ≤ ·)).image (coneTriangleBackIndex τ)) =
      I.filter (fun i => τ i = 1) := by
  rw [withoutLast_image_coneTriangleBackIndex]
  ext i
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hi, hsi⟩, ht⟩
    have hτ := τ.monotone hsi
    rw [hs1] at hτ
    exact ⟨hi, by omega⟩
  · rintro ⟨hi, hi1⟩
    have hne : i ≠ I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) := by
      intro he
      have ht := congrArg τ he
      rw [hi1, haz] at ht
      exact (by decide : (1 : Fin 3) ≠ 0) ht
    exact ⟨⟨hi, (I.erase (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))).min'_le i
      (Finset.mem_erase.mpr ⟨hne, hi⟩)⟩, by rw [hi1]; decide⟩
end SerrePositivity.EInfinity.ComplexLimits
