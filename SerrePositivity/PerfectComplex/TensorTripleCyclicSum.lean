module

public import SerrePositivity.PerfectComplex.TensorHomotopy
public import SerrePositivity.HomologicalAlgebra.CochainTensorShuffle
public import SerrePositivity.HomologicalAlgebra.CochainTensorHomogeneous
public import SerrePositivity.HomologicalAlgebra.CochainTensorTriple
public import SerrePositivity.PerfectComplex.CubicActionProjector

/-! # Cyclic permutation of the three tensor rotations -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Category Limits
variable {R : Type u} [CommRing R]

abbrev cochainTensorCyclicSum (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) :=
  cochainTensor (cochainTensor P Q) T ⊞
    (cochainTensor (cochainTensor T P) Q ⊞ cochainTensor (cochainTensor Q T) P)

def cochainTensorCyclicSumRotation (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainTensorCyclicSum P Q T ⟶ cochainTensorCyclicSum P Q T :=
  biprod.lift (biprod.snd ≫ biprod.snd ≫ (cochainTensorRotationIso Q T P).hom)
    (biprod.lift (biprod.fst ≫ (cochainTensorRotationIso P Q T).hom)
      (biprod.snd ≫ biprod.fst ≫ (cochainTensorRotationIso T P Q).hom))

lemma cochainTensorCyclicSumRotation_cube (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) :
    cochainTensorCyclicSumRotation P Q T ≫ cochainTensorCyclicSumRotation P Q T ≫
      cochainTensorCyclicSumRotation P Q T = 𝟙 _ := by
  apply biprod.hom_ext
  · simp only [cochainTensorCyclicSumRotation, Category.assoc, biprod.lift_fst,
      biprod.lift_fst_assoc, biprod.lift_snd_assoc,
      cochainTensorRotation_cube, comp_id, id_comp]
  · apply biprod.hom_ext
    · simp only [cochainTensorCyclicSumRotation, Category.assoc, biprod.lift_fst,
        biprod.lift_fst_assoc, biprod.lift_snd_assoc, biprod.lift_snd,
        cochainTensorRotation_cube, comp_id, id_comp]
    · simp only [cochainTensorCyclicSumRotation, Category.assoc,
        biprod.lift_fst_assoc, biprod.lift_snd_assoc, biprod.lift_snd,
        cochainTensorRotation_cube, comp_id, id_comp]

def cochainTensorCyclicSumAction (P Q T : CochainComplex (ModuleCat.{u} R) ℤ) :
    CochainCubicAction (cochainTensorCyclicSum P Q T) :=
  ⟨cochainTensorCyclicSumRotation P Q T, cochainTensorCyclicSumRotation_cube P Q T⟩

end SerrePositivity
