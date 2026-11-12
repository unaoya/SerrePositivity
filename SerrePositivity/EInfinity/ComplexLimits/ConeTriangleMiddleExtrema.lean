module
public import SerrePositivity.EInfinity.ComplexLimits.ConeTrianglePrincipalInjectivity

/-!
概要：元の中央相の部分集合の最小点・最大点を、元の second・penultimate に同定する。
方針：元の部分集合・全添字像・実評価射と端点の等式輸送を保持する。
規約：二つの主切断の非零成分比較は別工程。使われ方：大域評価三角形の混合 HA。
-/
@[expose] public section
namespace SerrePositivity.EInfinity.ComplexLimits


lemma middle_min_eq_second {n : ℕ} (τ : Fin (n + 1) →o Fin 3)
    (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (hs1 : τ (ConeHeadIndex.second I hI) = 1)
    (haz : τ (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) = 0) :
    (I.filter (fun i => τ i = 1)).min'
      (by exact ⟨_, Finset.mem_filter.mpr ⟨ConeHeadIndex.second_mem I hI, hs1⟩⟩) =
      ConeHeadIndex.second I hI := by
  let J := I.filter (fun i => τ i = 1)
  have hsJ : ConeHeadIndex.second I hI ∈ J :=
    Finset.mem_filter.mpr ⟨ConeHeadIndex.second_mem I hI, hs1⟩
  have hJ : J.Nonempty := ⟨_, hsJ⟩
  apply le_antisymm (J.min'_le _ hsJ)
  have hm := Finset.mem_filter.mp (J.min'_mem hJ)
  apply (I.erase (I.min' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))).min'_le _
  refine Finset.mem_erase.mpr ⟨?_, hm.1⟩
  intro he
  have ht := congrArg τ he
  rw [hm.2, haz] at ht
  exact (by decide : (1 : Fin 3) ≠ 0) ht

lemma middle_max_eq_penultimate {n : ℕ} (τ : Fin (n + 1) →o Fin 3)
    (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card)
    (hp1 : τ (ConeHeadIndex.penultimate I hI) = 1)
    (hbt : τ (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI)) = 2) :
    (I.filter (fun i => τ i = 1)).max'
      (by exact ⟨_, Finset.mem_filter.mpr ⟨ConeHeadIndex.penultimate_mem I hI, hp1⟩⟩) =
      ConeHeadIndex.penultimate I hI := by
  let J := I.filter (fun i => τ i = 1)
  have hpJ : ConeHeadIndex.penultimate I hI ∈ J :=
    Finset.mem_filter.mpr ⟨ConeHeadIndex.penultimate_mem I hI, hp1⟩
  have hJ : J.Nonempty := ⟨_, hpJ⟩
  apply le_antisymm ?_ (J.le_max' _ hpJ)
  have hm := Finset.mem_filter.mp (J.max'_mem hJ)
  apply (I.erase (I.max' (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Index.nonempty hI))).le_max' _
  refine Finset.mem_erase.mpr ⟨?_, hm.1⟩
  intro he
  have ht := congrArg τ he
  rw [hm.2, hbt] at ht
  exact (by decide : (1 : Fin 3) ≠ 2) ht
end SerrePositivity.EInfinity.ComplexLimits
