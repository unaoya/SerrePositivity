module

public import SerrePositivity.KTheory.Adams.TensorCubeFirstLayerSplitting

/-! # Sparse reconstruction of the first tensor-cube layer -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex Preadditive
variable {R : Type u} [CommRing R]

/-- Reconstruct the low pieces using one unrestricted quotient slot at a time. -/
lemma cochainTensorTripleDegreeMap_sparse_partition
    {P : CochainComplex (ModuleCat.{u} R) ℤ} (a b : ∀ i, P.X i ⟶ P.X i)
    (h : (fun i => a i + b i) = (fun i => 𝟙 (P.X i))) (n : ℤ) :
    cochainTensorTripleDegreeMap a a a n +
      cochainTensorTripleDegreeMap b (fun i => 𝟙 (P.X i)) (fun i => 𝟙 (P.X i)) n +
      cochainTensorTripleDegreeMap (fun i => 𝟙 (P.X i)) b (fun i => 𝟙 (P.X i)) n +
      cochainTensorTripleDegreeMap (fun i => 𝟙 (P.X i)) (fun i => 𝟙 (P.X i)) b n =
      𝟙 ((cochainTensor (cochainTensor P P) P).X n) +
        cochainTensorTripleDegreeMap b b a n + cochainTensorTripleDegreeMap b a b n +
        cochainTensorTripleDegreeMap a b b n + cochainTensorTripleDegreeMap b b b n +
        cochainTensorTripleDegreeMap b b b n := by
  have he := cochainTensorTripleDegreeMap_partition a b h n
  rw [← h]
  simp only [cochainTensorTripleDegreeMap_add_first,
    cochainTensorTripleDegreeMap_add_second, cochainTensorTripleDegreeMap_add_third]
  rw [← he]
  abel

namespace Adams
variable {P D : CochainComplex (ModuleCat.{u} R) ℤ}

lemma tensorCubeFirstLayerInclusion_sparse (q : P ⟶ D)
    (a : ∀ i, P.X i ⟶ P.X i) (s : ∀ i, D.X i ⟶ P.X i)
    (hp : (fun i => a i + q.f i ≫ s i) = (fun i => 𝟙 (P.X i))) (n : ℤ) :
    (tensorCubeFirstLayerInclusion q).f n ≫ cochainTensorTripleDegreeMap a a a n +
      (tensorCubeFirstLayerInclusion q).f n ≫ cochainTensorTripleDegreeMap
        (fun i => q.f i ≫ s i) (fun i => 𝟙 (P.X i)) (fun i => 𝟙 (P.X i)) n +
      (tensorCubeFirstLayerInclusion q).f n ≫ cochainTensorTripleDegreeMap
        (fun i => 𝟙 (P.X i)) (fun i => q.f i ≫ s i) (fun i => 𝟙 (P.X i)) n +
      (tensorCubeFirstLayerInclusion q).f n ≫ cochainTensorTripleDegreeMap
        (fun i => 𝟙 (P.X i)) (fun i => 𝟙 (P.X i)) (fun i => q.f i ≫ s i) n =
        (tensorCubeFirstLayerInclusion q).f n := by
  have he := congrArg (fun v => (tensorCubeFirstLayerInclusion q).f n ≫ v)
    (cochainTensorTripleDegreeMap_sparse_partition a (fun i => q.f i ≫ s i) hp n)
  simp only [comp_add, comp_id, tensorCubeFirstLayerInclusion_bbc_zero,
    tensorCubeFirstLayerInclusion_bcb_zero, tensorCubeFirstLayerInclusion_cbb_zero, add_zero] at he
  exact he

end Adams
end SerrePositivity
