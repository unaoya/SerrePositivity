module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PowerCokernelReconstruction
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerLiftNaturality

/-! # Naturality of the original power-cokernel reconstruction -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
variable {R : Type u} [CommRing R] (a : R)
  {K L : CochainComplex (ModuleCat.{u} R) ℤ}

/-- The map of the actual power cokernels, induced by the original complex map. -/
def powerCokernelMap (f : K ⟶ L) (n : ℕ) :
    powerCokernelComplex a K n ⟶ powerCokernelComplex a L n :=
  cokernel.map _ _ f f (by simp [smulId, Linear.smul_comp, Linear.comp_smul])

@[reassoc] lemma powerCokernelMap_π (f : K ⟶ L) (n : ℕ) :
    cokernel.π (smulId (a ^ n) K) ≫ powerCokernelMap a f n =
      f ≫ cokernel.π (smulId (a ^ n) L) := by
  simp [powerCokernelMap, cokernel.map]

@[reassoc] lemma powerCokernelMap_transition (f : K ⟶ L) (n : ℕ) :
    powerCokernelComplexTransition a K n ≫ powerCokernelMap a f n =
      powerCokernelMap a f (n + 1) ≫ powerCokernelComplexTransition a L n := by
  apply (cancel_epi (cokernel.π (smulId (a ^ (n + 1)) K))).mp
  rw [← Category.assoc, powerCokernelComplexTransition_π, powerCokernelMap_π,
    ← Category.assoc, powerCokernelMap_π, Category.assoc, powerCokernelComplexTransition_π]

/-- The original tower map for an arbitrary coefficient-complex map. -/
def powerCokernelHolimMap (f : K ⟶ L) :
    complexTowerHomotopyLimit R (powerCokernelComplex a K) (powerCokernelComplexTransition a K) ⟶
      complexTowerHomotopyLimit R (powerCokernelComplex a L) (powerCokernelComplexTransition a L) :=
  complexTowerHomotopyLimitMap R _ _ (powerCokernelMap a f) (powerCokernelMap_transition a f)

/-- Reconstruction intertwines arbitrary original complex maps and their holim maps. -/
@[reassoc] lemma powerCokernelReconstruction_naturality (f : K ⟶ L) :
    powerCokernelReconstruction a K ≫ powerCokernelHolimMap a f =
      f ≫ powerCokernelReconstruction a L := by
  rw [powerCokernelReconstruction_eq_lift, powerCokernelReconstruction_eq_lift]
  exact complexTowerCompatibleLift_naturality R _ _ _ _ _ f _ _ _ _ (powerCokernelMap_π a f)

end SerrePositivity.DerivedCompletion
