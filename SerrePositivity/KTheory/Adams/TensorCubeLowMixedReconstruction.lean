module

public import SerrePositivity.KTheory.Adams.TensorCubeLowMixedSections
public import SerrePositivity.KTheory.Adams.TensorCubeSparsePartition

/-! # Reconstruction of the low tensor-cube filtration layer -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex Preadditive
namespace Adams
variable {R : Type u} [CommRing R]
variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting)

/-- Retract onto AAA by the degreewise retraction in all three positions. -/
def tensorCubeLowMixedRetractionX (n : ℤ) :
    (tensorCubeFirstLayer S.g).X n ⟶ (tensorCube S.X₁).X n :=
  (tensorCubeFirstLayerInclusion S.g).f n ≫
    cochainTensorTripleDegreeMap (cochainSplittingRetraction S σ)
      (cochainSplittingRetraction S σ) (cochainSplittingRetraction S σ) n

lemma tensorCubeLowMixedRetractionX_retract (n : ℤ) :
    (tensorCubeFirstLayerFirstMap S).f n ≫ tensorCubeLowMixedRetractionX S σ n = 𝟙 _ := by
  rw [tensorCubeLowMixedRetractionX, ← HomologicalComplex.comp_f_assoc,
    tensorCubeFirstLayerFirstMap_inclusion,
    ← cochainTensorTripleDegreeMap_eq S.f S.f S.f n, cochainTensorTripleDegreeMap_comp]
  have he : (fun i => S.f.f i ≫ cochainSplittingRetraction S σ i) =
      (fun i => 𝟙 (S.X₁.X i)) := funext fun i => (σ i).f_r
  rw [he, cochainTensorTripleDegreeMap_id]

lemma tensorCubeLowMixedRetractionX_first_inclusion (n : ℤ) :
    tensorCubeLowMixedRetractionX S σ n ≫ (tensorCubeFirstLayerFirstMap S).f n ≫
      (tensorCubeFirstLayerInclusion S.g).f n =
    (tensorCubeFirstLayerInclusion S.g).f n ≫
      cochainTensorTripleDegreeMap (tensorCubeSplittingA S σ)
        (tensorCubeSplittingA S σ) (tensorCubeSplittingA S σ) n := by
  rw [← HomologicalComplex.comp_f, tensorCubeFirstLayerFirstMap_inclusion,
    tensorCubeLowMixedRetractionX, Category.assoc,
    ← cochainTensorTripleDegreeMap_eq S.f S.f S.f n, cochainTensorTripleDegreeMap_comp]

variable (hS : S.ShortExact) (hproj : ∀ i, Module.Projective R (S.X₃.X i))

lemma tensorCubeLowMixed0_section_inclusion (n : ℤ) :
    (tensorCubeLowMixed0 S hS hproj).f n ≫ tensorCubeLowMixedSection0X S σ n ≫
      (tensorCubeFirstLayerInclusion S.g).f n =
    (tensorCubeFirstLayerInclusion S.g).f n ≫ cochainTensorTripleDegreeMap
      (tensorCubeSplittingB S σ) (fun i => 𝟙 (S.X₂.X i)) (fun i => 𝟙 (S.X₂.X i)) n := by
  rw [tensorCubeLowMixedSection0X_inclusion]
  have he : tensorCubeLowMixedRawSection0X S σ n =
      (cochainTensorTripleMap (𝟙 S.X₃) S.f S.f).f n ≫
        cochainTensorTripleDegreeMap (cochainSplittingSection S σ)
          (fun i => 𝟙 (S.X₂.X i)) (fun i => 𝟙 (S.X₂.X i)) n := by
    rw [← cochainTensorTripleDegreeMap_eq (𝟙 S.X₃) S.f S.f n,
      cochainTensorTripleDegreeMap_comp]
    simp only [tensorCubeLowMixedRawSection0X, HomologicalComplex.id_f, comp_id, id_comp]
  rw [he, ← Category.assoc, ← HomologicalComplex.comp_f,
    tensorCubeLowMixed0_inclusion,
    HomologicalComplex.comp_f, Category.assoc,
    ← cochainTensorTripleDegreeMap_eq S.g (𝟙 S.X₂) (𝟙 S.X₂) n, cochainTensorTripleDegreeMap_comp]
  simp only [HomologicalComplex.id_f, id_comp]

lemma tensorCubeLowMixed1_section_inclusion (n : ℤ) :
    (tensorCubeLowMixed1 S hS hproj).f n ≫ tensorCubeLowMixedSection1X S σ n ≫
      (tensorCubeFirstLayerInclusion S.g).f n =
    (tensorCubeFirstLayerInclusion S.g).f n ≫ cochainTensorTripleDegreeMap
      (fun i => 𝟙 (S.X₂.X i)) (tensorCubeSplittingB S σ) (fun i => 𝟙 (S.X₂.X i)) n := by
  rw [tensorCubeLowMixedSection1X_inclusion]
  have he : tensorCubeLowMixedRawSection1X S σ n =
      (cochainTensorTripleMap S.f (𝟙 S.X₃) S.f).f n ≫
        cochainTensorTripleDegreeMap (fun i => 𝟙 (S.X₂.X i))
          (cochainSplittingSection S σ) (fun i => 𝟙 (S.X₂.X i)) n := by
    rw [← cochainTensorTripleDegreeMap_eq S.f (𝟙 S.X₃) S.f n,
      cochainTensorTripleDegreeMap_comp]
    simp only [tensorCubeLowMixedRawSection1X, HomologicalComplex.id_f, comp_id, id_comp]
  rw [he, ← Category.assoc, ← HomologicalComplex.comp_f,
    tensorCubeLowMixed1_inclusion,
    HomologicalComplex.comp_f, Category.assoc,
    ← cochainTensorTripleDegreeMap_eq (𝟙 S.X₂) S.g (𝟙 S.X₂) n, cochainTensorTripleDegreeMap_comp]
  simp only [HomologicalComplex.id_f, id_comp]

lemma tensorCubeLowMixed2_section_inclusion (n : ℤ) :
    (tensorCubeLowMixed2 S hS hproj).f n ≫ tensorCubeLowMixedSection2X S σ n ≫
      (tensorCubeFirstLayerInclusion S.g).f n =
    (tensorCubeFirstLayerInclusion S.g).f n ≫ cochainTensorTripleDegreeMap
      (fun i => 𝟙 (S.X₂.X i)) (fun i => 𝟙 (S.X₂.X i)) (tensorCubeSplittingB S σ) n := by
  rw [tensorCubeLowMixedSection2X_inclusion]
  have he : tensorCubeLowMixedRawSection2X S σ n =
      (cochainTensorTripleMap S.f S.f (𝟙 S.X₃)).f n ≫
        cochainTensorTripleDegreeMap (fun i => 𝟙 (S.X₂.X i))
          (fun i => 𝟙 (S.X₂.X i)) (cochainSplittingSection S σ) n := by
    rw [← cochainTensorTripleDegreeMap_eq S.f S.f (𝟙 S.X₃) n,
      cochainTensorTripleDegreeMap_comp]
    simp only [tensorCubeLowMixedRawSection2X, HomologicalComplex.id_f, comp_id, id_comp]
  rw [he, ← Category.assoc, ← HomologicalComplex.comp_f,
    tensorCubeLowMixed2_inclusion,
    HomologicalComplex.comp_f, Category.assoc,
    ← cochainTensorTripleDegreeMap_eq (𝟙 S.X₂) (𝟙 S.X₂) S.g n, cochainTensorTripleDegreeMap_comp]
  simp only [HomologicalComplex.id_f, id_comp]

/-- AAA and the three low mixed components reconstruct the first intermediate layer. -/
lemma tensorCubeLowMixedSplitting_total (n : ℤ) :
    tensorCubeLowMixedRetractionX S σ n ≫ (tensorCubeFirstLayerFirstMap S).f n +
      (tensorCubeLowMixed0 S hS hproj).f n ≫ tensorCubeLowMixedSection0X S σ n +
      (tensorCubeLowMixed1 S hS hproj).f n ≫ tensorCubeLowMixedSection1X S σ n +
      (tensorCubeLowMixed2 S hS hproj).f n ≫ tensorCubeLowMixedSection2X S σ n =
        𝟙 ((tensorCubeFirstLayer S.g).X n) := by
  apply (cancel_mono ((tensorCubeFirstLayerInclusion S.g).f n)).mp
  rw [add_comp, add_comp, add_comp, Category.assoc, Category.assoc, Category.assoc,
    Category.assoc, tensorCubeLowMixedRetractionX_first_inclusion,
    tensorCubeLowMixed0_section_inclusion, tensorCubeLowMixed1_section_inclusion,
    tensorCubeLowMixed2_section_inclusion, id_comp]
  exact tensorCubeFirstLayerInclusion_sparse S.g (tensorCubeSplittingA S σ)
    (cochainSplittingSection S σ) (funext fun i => (σ i).id) n

end Adams
end SerrePositivity
