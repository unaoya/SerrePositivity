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
