module

public import SerrePositivity.PerfectComplex.CubicActionEigenvectors
public import SerrePositivity.PerfectComplex.BiproductPerfect

/-! # The standard cyclic action on three copies of a complex -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Category Limits Preadditive
variable {R : Type u} [CommRing R]
variable (U : CochainComplex (ModuleCat.{u} R) ℤ)

abbrev cochainCyclicThree := U ⊞ (U ⊞ U)

/-- Right cyclic permutation of three copies. -/
def cochainCyclicThreeRotation : cochainCyclicThree U ⟶ cochainCyclicThree U :=
  biprod.lift (biprod.snd ≫ biprod.snd) (biprod.lift biprod.fst (biprod.snd ≫ biprod.fst))

lemma cochainCyclicThreeRotation_cube :
    cochainCyclicThreeRotation U ≫ cochainCyclicThreeRotation U ≫
      cochainCyclicThreeRotation U = 𝟙 _ := by
  apply biprod.hom_ext
  · simp [cochainCyclicThreeRotation, Category.assoc]
  · apply biprod.hom_ext
    · simp [cochainCyclicThreeRotation, Category.assoc]
    · simp [cochainCyclicThreeRotation, Category.assoc]

def cochainCyclicThreeAction : CochainCubicAction (cochainCyclicThree U) :=
  ⟨cochainCyclicThreeRotation U, cochainCyclicThreeRotation_cube U⟩

/-- The eigenvector with first coordinate x has remaining coordinates a²x and ax. -/
def cochainCyclicThreeVector (a : R) : U ⟶ cochainCyclicThree U :=
  biprod.lift (𝟙 U) (biprod.lift (a ^ 2 • 𝟙 U) (a • 𝟙 U))

lemma cochainCyclicThreeVector_first (a : R) :
    cochainCyclicThreeVector U a ≫ biprod.fst = 𝟙 U := by
  simp only [cochainCyclicThreeVector, biprod.lift_fst]

lemma cochainCyclicThreeVector_eigen (a : R) (ha : a ^ 3 = 1) :
    cochainCyclicThreeVector U a ≫ cochainCyclicThreeRotation U =
      a • cochainCyclicThreeVector U a := by
  have hac : a * a ^ 2 = 1 := by rw [← pow_succ', ha]
  apply biprod.hom_ext
  · simp [cochainCyclicThreeVector, cochainCyclicThreeRotation, Category.assoc,
      Linear.smul_comp]
  · apply biprod.hom_ext
    · simp [cochainCyclicThreeVector, cochainCyclicThreeRotation, Category.assoc,
        Linear.smul_comp, smul_smul, hac]
    · simp [cochainCyclicThreeVector, cochainCyclicThreeRotation, Category.assoc,
        Linear.smul_comp, smul_smul, ← pow_two]

lemma cochainCyclicThreeVector_reconstruction (a : R)
    {L : CochainComplex (ModuleCat.{u} R) ℤ} (v : L ⟶ cochainCyclicThree U)
    (hv : v ≫ cochainCyclicThreeRotation U = a • v) :
    (v ≫ biprod.fst) ≫ cochainCyclicThreeVector U a = v := by
  have h₂ : v ≫ biprod.snd ≫ biprod.snd = a • (v ≫ biprod.fst) := by
    simpa only [cochainCyclicThreeRotation, Category.assoc, biprod.lift_fst,
      Linear.smul_comp] using hv =≫ biprod.fst
  have h₁ : v ≫ biprod.snd ≫ biprod.fst = a ^ 2 • (v ≫ biprod.fst) := by
    have h : v ≫ biprod.snd ≫ biprod.fst = a • (v ≫ biprod.snd ≫ biprod.snd) := by
      simpa only [cochainCyclicThreeRotation, Category.assoc, biprod.lift_snd_assoc,
        biprod.lift_snd, Linear.smul_comp] using hv =≫ (biprod.snd ≫ biprod.snd)
    rw [h, h₂, smul_smul, ← pow_two]
  apply biprod.hom_ext
  · simp only [Category.assoc, cochainCyclicThreeVector, biprod.lift_fst, comp_id]
  · apply biprod.hom_ext
    · simpa only [Category.assoc, cochainCyclicThreeVector, biprod.lift_snd_assoc,
        biprod.lift_fst, Linear.comp_smul, comp_id] using h₁.symm
    · simpa only [Category.assoc, cochainCyclicThreeVector, biprod.lift_snd_assoc,
        biprod.lift_snd, Linear.comp_smul, comp_id] using h₂.symm

/-- Every Fourier eigenspace of the standard three-copy action is the original complex. -/
def cochainCyclicThreeEigenIso [Invertible (3 : R)] (a : R) (ha : a ^ 3 = 1) :
    ((cochainCyclicThreeAction U).projector a ha).image ≅ U where
  hom := ((cochainCyclicThreeAction U).projector a ha).inclusion ≫ biprod.fst
  inv := (cochainCyclicThreeAction U).eigenvectorLift a ha (cochainCyclicThreeVector U a)
    (cochainCyclicThreeVector_eigen U a ha)
  hom_inv_id := by
    apply (cancel_mono ((cochainCyclicThreeAction U).projector a ha).inclusion).mp
    rw [Category.assoc, CochainCubicAction.eigenvectorLift_inclusion, id_comp]
    exact cochainCyclicThreeVector_reconstruction U a _
      ((cochainCyclicThreeAction U).projector_inclusion_eigen a ha)
  inv_hom_id := by
    rw [← Category.assoc, CochainCubicAction.eigenvectorLift_inclusion,
      cochainCyclicThreeVector_first]

end SerrePositivity
