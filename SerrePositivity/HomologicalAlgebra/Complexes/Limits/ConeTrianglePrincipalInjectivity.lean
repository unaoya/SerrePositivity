module
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ConeTriangleSupport
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ConeSecond
public import SerrePositivity.HomologicalAlgebra.Complexes.Limits.ConePenultimate

/-!
概要：主場合の始点相・終点相の一意性から、元の両三角形添字の単射性を得る。
方針：元の部分集合・全添字像・実評価射と端点の等式輸送を保持する。
規約：二つの主切断の非零成分比較は別工程。使われ方：大域評価三角形の混合 HA。
-/
@[expose] public section
namespace SerrePositivity.ComplexLimits


lemma eq_min_of_second_one {n : ℕ} (τ : Fin (n + 1) →o Fin 3)
    (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (hs1 : τ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.second I hI) = 1) (i : Fin (n + 1))
    (hi : i ∈ I) (hz : τ i = 0) : i = I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) := by
  by_contra hne
  have hsi : _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.second I hI ≤ i :=
    (I.erase (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))).min'_le i (Finset.mem_erase.mpr ⟨hne, hi⟩)
  have ht := τ.monotone hsi
  rw [hs1, hz] at ht
  exact (by decide : ¬ (1 : Fin 3) ≤ 0) ht

lemma eq_max_of_penultimate_one {n : ℕ} (τ : Fin (n + 1) →o Fin 3)
    (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (hp1 : τ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI) = 1) (i : Fin (n + 1))
    (hi : i ∈ I) (ht : τ i = 2) : i = I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI) := by
  by_contra hne
  have hip : i ≤ _root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI :=
    (I.erase (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))).le_max' i (Finset.mem_erase.mpr ⟨hne, hi⟩)
  have hτ := τ.monotone hip
  rw [ht, hp1] at hτ
  exact (by decide : ¬ (2 : Fin 3) ≤ 1) hτ

lemma coneTriangleFrontIndex_injOn_of_second_one {n : ℕ} (τ : Fin (n + 1) →o Fin 3)
    (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (hs1 : τ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.second I hI) = 1) :
    Set.InjOn (_root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex τ) (I : Set (Fin (n + 1))) := by
  apply (_root_.SerrePositivity.ComplexLimits.coneTriangleFrontIndex_injOn_iff τ _).mpr
  intro i hi j hj hti htj
  exact (_root_.SerrePositivity.ComplexLimits.eq_min_of_second_one τ I hI hs1 i hi hti).trans
    (_root_.SerrePositivity.ComplexLimits.eq_min_of_second_one τ I hI hs1 j hj htj).symm

lemma coneTriangleBackIndex_injOn_of_penultimate_one {n : ℕ} (τ : Fin (n + 1) →o Fin 3)
    (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (hp1 : τ (_root_.SerrePositivity.ComplexLimits.ConeHeadIndex.penultimate I hI) = 1) :
    Set.InjOn (_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex τ) (I : Set (Fin (n + 1))) := by
  apply (_root_.SerrePositivity.ComplexLimits.coneTriangleBackIndex_injOn_iff τ _).mpr
  intro i hi j hj hti htj
  exact (_root_.SerrePositivity.ComplexLimits.eq_max_of_penultimate_one τ I hI hp1 i hi hti).trans
    (_root_.SerrePositivity.ComplexLimits.eq_max_of_penultimate_one τ I hI hp1 j hj htj).symm
end SerrePositivity.ComplexLimits
