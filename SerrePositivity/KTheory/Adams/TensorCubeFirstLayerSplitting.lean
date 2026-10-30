module

public import SerrePositivity.KTheory.Adams.TensorCubeFirstLayer
public import SerrePositivity.HomologicalAlgebra.CochainTensorLinear
public import SerrePositivity.HomologicalAlgebra.CochainTensorDegreeMaps
public import SerrePositivity.PerfectComplex.TensorHomotopy
public import SerrePositivity.HomologicalAlgebra.CochainTensorShuffle
public import SerrePositivity.HomologicalAlgebra.CochainTensorHomogeneous
public import SerrePositivity.HomologicalAlgebra.CochainTensorTriple
public import SerrePositivity.HomologicalAlgebra.CochainTensorTripleDegreeMaps
public import SerrePositivity.PerfectComplex.IdempotentImagePerfect
public import SerrePositivity.HomologicalAlgebra.CochainBiproduct
public import SerrePositivity.HomologicalAlgebra.CochainIdempotentDecomposition
public import SerrePositivity.HomologicalAlgebra.CochainKernelLift

/-! # The four low-degree components of the tensor-cube first layer -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex Preadditive
namespace Adams
variable {R : Type u} [CommRing R]
variable {P D : CochainComplex (ModuleCat.{u} R) ℤ}

/-- Keep the four graded components containing at most one quotient factor. -/
def tensorCubeLowDegreeMap (a b : ∀ i, P.X i ⟶ P.X i) (n : ℤ) :
    (tensorCube P).X n ⟶ (tensorCube P).X n :=
  cochainTensorTripleDegreeMap a a a n + cochainTensorTripleDegreeMap b a a n +
    cochainTensorTripleDegreeMap a b a n + cochainTensorTripleDegreeMap a a b n

lemma tensorCubeLowDegreeMap_pair0 (q : P ⟶ D) (a b : ∀ i, P.X i ⟶ P.X i)
    (ha : (fun i => a i ≫ q.f i) = (fun i => (0 : P.X i ⟶ D.X i))) (n : ℤ) :
    tensorCubeLowDegreeMap a b n ≫ (tensorCubePairMap0 q).f n = 0 := by
  rw [← cochainTensorTripleDegreeMap_eq q q (𝟙 P) n]
  simp only [tensorCubeLowDegreeMap, add_comp, cochainTensorTripleDegreeMap_comp, ha,
    cochainTensorTripleDegreeMap_zero_first, cochainTensorTripleDegreeMap_zero_second,
    add_zero]

lemma tensorCubeLowDegreeMap_pair1 (q : P ⟶ D) (a b : ∀ i, P.X i ⟶ P.X i)
    (ha : (fun i => a i ≫ q.f i) = (fun i => (0 : P.X i ⟶ D.X i))) (n : ℤ) :
    tensorCubeLowDegreeMap a b n ≫ (tensorCubePairMap1 q).f n = 0 := by
  rw [← cochainTensorTripleDegreeMap_eq (𝟙 P) q q n]
  simp only [tensorCubeLowDegreeMap, add_comp, cochainTensorTripleDegreeMap_comp, ha,
    cochainTensorTripleDegreeMap_zero_second, cochainTensorTripleDegreeMap_zero_third,
    add_zero]

lemma tensorCubeLowDegreeMap_pair2 (q : P ⟶ D) (a b : ∀ i, P.X i ⟶ P.X i)
    (ha : (fun i => a i ≫ q.f i) = (fun i => (0 : P.X i ⟶ D.X i))) (n : ℤ) :
    tensorCubeLowDegreeMap a b n ≫ (tensorCubePairMap2 q).f n = 0 := by
  rw [← cochainTensorTripleDegreeMap_eq q (𝟙 P) q n]
  simp only [tensorCubeLowDegreeMap, add_comp, cochainTensorTripleDegreeMap_comp, ha,
    cochainTensorTripleDegreeMap_zero_first, cochainTensorTripleDegreeMap_zero_third,
    add_zero]

lemma tensorCubeLowDegreeMap_pairMap (q : P ⟶ D) (a b : ∀ i, P.X i ⟶ P.X i)
    (ha : (fun i => a i ≫ q.f i) = (fun i => (0 : P.X i ⟶ D.X i))) (n : ℤ) :
    tensorCubeLowDegreeMap a b n ≫ (tensorCubePairMap q).f n = 0 := by
  apply cochainBiprodDegree_hom_ext
    (cochainTensor (cochainTensor D D) P)
    (cochainTensor (cochainTensor P D) D ⊞ cochainTensor (cochainTensor D P) D) n
  · rw [Category.assoc, ← HomologicalComplex.comp_f, tensorCubePairMap, biprod.lift_fst]
    simpa only [zero_comp] using tensorCubeLowDegreeMap_pair0 q a b ha n
  · apply cochainBiprodDegree_hom_ext (cochainTensor (cochainTensor P D) D)
      (cochainTensor (cochainTensor D P) D) n
    · rw [Category.assoc, Category.assoc, ← HomologicalComplex.comp_f,
        ← HomologicalComplex.comp_f, tensorCubePairMap, biprod.lift_snd_assoc, biprod.lift_fst]
      simpa only [zero_comp] using tensorCubeLowDegreeMap_pair1 q a b ha n
    · rw [Category.assoc, Category.assoc, ← HomologicalComplex.comp_f,
        ← HomologicalComplex.comp_f, tensorCubePairMap, biprod.lift_snd_assoc, biprod.lift_snd]
      simpa only [zero_comp] using tensorCubeLowDegreeMap_pair2 q a b ha n

lemma tensorCubeFirstLayerInclusion_bbc_zero (q : P ⟶ D)
    (s : ∀ i, D.X i ⟶ P.X i) (c : ∀ i, P.X i ⟶ P.X i) (n : ℤ) :
    (tensorCubeFirstLayerInclusion q).f n ≫
      cochainTensorTripleDegreeMap (fun i => q.f i ≫ s i) (fun i => q.f i ≫ s i) c n = 0 := by
  have he : (tensorCubePairMap0 q).f n ≫ cochainTensorTripleDegreeMap s s c n =
      cochainTensorTripleDegreeMap (fun i => q.f i ≫ s i) (fun i => q.f i ≫ s i) c n := by
    rw [← cochainTensorTripleDegreeMap_eq q q (𝟙 P) n, cochainTensorTripleDegreeMap_comp]
    simp only [HomologicalComplex.id_f, id_comp]
  rw [← he, ← Category.assoc, ← HomologicalComplex.comp_f,
    tensorCubeFirstLayerInclusion_pair0, HomologicalComplex.zero_f, zero_comp]

lemma tensorCubeFirstLayerInclusion_bcb_zero (q : P ⟶ D)
    (s : ∀ i, D.X i ⟶ P.X i) (c : ∀ i, P.X i ⟶ P.X i) (n : ℤ) :
    (tensorCubeFirstLayerInclusion q).f n ≫
      cochainTensorTripleDegreeMap (fun i => q.f i ≫ s i) c (fun i => q.f i ≫ s i) n = 0 := by
  have he : (tensorCubePairMap2 q).f n ≫ cochainTensorTripleDegreeMap s c s n =
      cochainTensorTripleDegreeMap (fun i => q.f i ≫ s i) c (fun i => q.f i ≫ s i) n := by
    rw [← cochainTensorTripleDegreeMap_eq q (𝟙 P) q n, cochainTensorTripleDegreeMap_comp]
    simp only [HomologicalComplex.id_f, id_comp]
  rw [← he, ← Category.assoc, ← HomologicalComplex.comp_f,
    tensorCubeFirstLayerInclusion_pair2, HomologicalComplex.zero_f, zero_comp]

lemma tensorCubeFirstLayerInclusion_cbb_zero (q : P ⟶ D)
    (s : ∀ i, D.X i ⟶ P.X i) (c : ∀ i, P.X i ⟶ P.X i) (n : ℤ) :
    (tensorCubeFirstLayerInclusion q).f n ≫
      cochainTensorTripleDegreeMap c (fun i => q.f i ≫ s i) (fun i => q.f i ≫ s i) n = 0 := by
  have he : (tensorCubePairMap1 q).f n ≫ cochainTensorTripleDegreeMap c s s n =
      cochainTensorTripleDegreeMap c (fun i => q.f i ≫ s i) (fun i => q.f i ≫ s i) n := by
    rw [← cochainTensorTripleDegreeMap_eq (𝟙 P) q q n, cochainTensorTripleDegreeMap_comp]
    simp only [HomologicalComplex.id_f, id_comp]
  rw [← he, ← Category.assoc, ← HomologicalComplex.comp_f,
    tensorCubeFirstLayerInclusion_pair1, HomologicalComplex.zero_f, zero_comp]

/-- On the common kernel the four low components reconstruct the inclusion. -/
lemma tensorCubeFirstLayerInclusion_low (q : P ⟶ D) (a : ∀ i, P.X i ⟶ P.X i)
    (s : ∀ i, D.X i ⟶ P.X i)
    (hp : (fun i => a i + q.f i ≫ s i) = (fun i => 𝟙 (P.X i))) (n : ℤ) :
    (tensorCubeFirstLayerInclusion q).f n ≫
      tensorCubeLowDegreeMap a (fun i => q.f i ≫ s i) n =
        (tensorCubeFirstLayerInclusion q).f n := by
  let b := fun i => q.f i ≫ s i
  have he := congrArg (fun v => (tensorCubeFirstLayerInclusion q).f n ≫ v)
    (cochainTensorTripleDegreeMap_partition a b hp n)
  simp only [b, comp_add, comp_id, tensorCubeFirstLayerInclusion_bbc_zero,
    tensorCubeFirstLayerInclusion_bcb_zero, tensorCubeFirstLayerInclusion_cbb_zero,
    add_zero] at he
  rw [tensorCubeLowDegreeMap, comp_add, comp_add, comp_add]
  exact he

variable (S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ))
    (σ : ∀ i, (S.map (eval _ _ i)).Splitting)

abbrev tensorCubeSplittingA (i : ℤ) : S.X₂.X i ⟶ S.X₂.X i :=
  cochainSplittingRetraction S σ i ≫ S.f.f i
abbrev tensorCubeSplittingB (i : ℤ) : S.X₂.X i ⟶ S.X₂.X i :=
  S.g.f i ≫ cochainSplittingSection S σ i

lemma tensorCubeSplittingA_quotient_zero :
    (fun i => tensorCubeSplittingA S σ i ≫ S.g.f i) =
      (fun i => (0 : S.X₂.X i ⟶ S.X₃.X i)) := by
  funext i
  rw [tensorCubeSplittingA, Category.assoc, ← HomologicalComplex.comp_f,
    S.zero, HomologicalComplex.zero_f, comp_zero]

/-- The graded four-component projection lifted into the common kernel. -/
def tensorCubeFirstLayerRetractionX (n : ℤ) :
    (tensorCube S.X₂).X n ⟶ (tensorCubeFirstLayer S.g).X n :=
  cochainKernelLiftX (tensorCubePairMap S.g) n
    (tensorCubeLowDegreeMap (tensorCubeSplittingA S σ) (tensorCubeSplittingB S σ) n)
    (tensorCubeLowDegreeMap_pairMap S.g _ _ (tensorCubeSplittingA_quotient_zero S σ) n)

@[reassoc]
lemma tensorCubeFirstLayerRetractionX_inclusion (n : ℤ) :
    tensorCubeFirstLayerRetractionX S σ n ≫ (tensorCubeFirstLayerInclusion S.g).f n =
      tensorCubeLowDegreeMap (tensorCubeSplittingA S σ) (tensorCubeSplittingB S σ) n :=
  cochainKernelLiftX_inclusion _ _ _ _

lemma tensorCubeFirstLayerRetractionX_retract (n : ℤ) :
    (tensorCubeFirstLayerInclusion S.g).f n ≫ tensorCubeFirstLayerRetractionX S σ n = 𝟙 _ := by
  apply (cancel_mono ((tensorCubeFirstLayerInclusion S.g).f n)).mp
  rw [Category.assoc, tensorCubeFirstLayerRetractionX_inclusion, id_comp]
  exact tensorCubeFirstLayerInclusion_low S.g _ (cochainSplittingSection S σ)
    (funext fun i => (σ i).id) n

lemma tensorCubeFirstLayer_perfect (hS : S.ShortExact)
    (hp : strictlyPerfectComplex R S.X₂) (hd : strictlyPerfectComplex R S.X₃) :
    strictlyPerfectComplex R (tensorCubeFirstLayer S.g) := by
  let σ := cochainDegreewiseSplittingOfProjective S hS (fun i => (hd.2 i).2)
  exact strictlyPerfectComplex_of_degreewiseRetract (tensorCubeFirstLayerInclusion S.g)
    (tensorCubeFirstLayerRetractionX S σ) (tensorCubeFirstLayerRetractionX_retract S σ)
    (tensorCube_perfect S.X₂ hp)

end Adams
end SerrePositivity
