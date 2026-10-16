module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.ModulePowerTensorModel
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.BoundedTermTorsionComparison
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.TowerIsoMapCompatibility

/-! # Standard reconstruction from the ordinary module power-quotient tensor tower -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.DerivedCompletion
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R] (a : R) (M : ModuleCat.{u} R)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)

/-- The tower consists of the actual ordinary quotients tensored with the fixed model. -/
abbrev modulePowerTensorTower (n : ℕ) : CochainComplex (ModuleCat.{u} R) ℤ :=
  (moduleTensorCochainFunctor K).obj (modulePowerReduction a M n)

def modulePowerTensorTransition (n : ℕ) :
    modulePowerTensorTower a M K (n + 1) ⟶ modulePowerTensorTower a M K n :=
  (moduleTensorCochainFunctor K).map (modulePowerReductionTransition a M n)

lemma modulePowerTensorReductionMap_transition (n : ℕ) :
    modulePowerTensorReductionMap a M K (n + 1) ≫ modulePowerTensorTransition a M K n =
      modulePowerTensorReductionMap a M K n := by
  simp only [modulePowerTensorReductionMap, modulePowerTensorTransition,
    ← Functor.map_comp, modulePowerReductionTransition_π]

/-- The original compatible quotient maps define the reconstruction itself. -/
def modulePowerTensorReconstruction :
    (moduleTensorCochainFunctor K).obj M ⟶
      complexTowerHomotopyLimit R (modulePowerTensorTower a M K)
        (modulePowerTensorTransition a M K) :=
  complexTowerCompatibleLift R _ _ _ (modulePowerTensorReductionMap a M K)
    (modulePowerTensorReductionMap_transition a M K)

@[reassoc] lemma modulePowerTensorReconstruction_projection (n : ℕ) :
    modulePowerTensorReconstruction a M K ≫
      complexTowerProjection R (modulePowerTensorTower a M K) (modulePowerTensorTransition a M K) ≫
        Pi.π (modulePowerTensorTower a M K) n = modulePowerTensorReductionMap a M K n := by
  rw [modulePowerTensorReconstruction, ← Category.assoc,
    complexTowerCompatibleLift_comp_projection, Pi.lift_comp_π]

/-- The existing ordinary cokernel tower and the actual quotient tensor tower
have canonically isomorphic holims. -/
def modulePowerCokernelHolimIso (hK : ∀ i, Module.Flat R (K.X i)) :
    complexTowerHomotopyLimit R
      (powerCokernelComplex a ((moduleTensorCochainFunctor K).obj M))
      (powerCokernelComplexTransition a ((moduleTensorCochainFunctor K).obj M)) ≅
    complexTowerHomotopyLimit R (modulePowerTensorTower a M K)
      (modulePowerTensorTransition a M K) :=
  complexTowerHomotopyLimitIso R _ _ (modulePowerTensorModelIso a M K hK)
    (modulePowerTensorModelIso_transition a M K hK)

/-- The holim comparison transports the original reconstruction to the original
quotient lift, not just to an isomorphic unspecified map. -/
@[reassoc] lemma powerCokernelReconstruction_comp_modulePowerHolimIso
    (hK : ∀ i, Module.Flat R (K.X i)) :
    powerCokernelReconstruction a ((moduleTensorCochainFunctor K).obj M) ≫
      (modulePowerCokernelHolimIso a M K hK).hom = modulePowerTensorReconstruction a M K := by
  rw [powerCokernelReconstruction_eq_lift]
  exact complexTowerCompatibleLift_iso R _ _ (modulePowerTensorModelIso a M K hK)
    (modulePowerTensorModelIso_transition a M K hK) _ _
    (powerCokernelComplexTransition_π a ((moduleTensorCochainFunctor K).obj M)) _
    (modulePowerTensorReductionMap_transition a M K) (modulePowerTensorModelIso_π a M K hK)

/-- A common torsion bound and actual completeness prove that the standard
quotient lift is a quasi-isomorphism. -/
lemma modulePowerTensorReconstruction_quasiIso
    (hK : ∀ i, Module.Flat R (K.X i)) (N : ℕ)
    (h : ∀ (i : ℤ) (n : ℕ) (x : ((moduleTensorCochainFunctor K).obj M).X i),
      a ^ n • x = 0 → a ^ N • x = 0)
    (hc : IsComplete R a (DerivedCategory.Q.obj ((moduleTensorCochainFunctor K).obj M))) :
    QuasiIso (modulePowerTensorReconstruction a M K) := by
  have := powerCokernelReconstruction_quasiIso_of_term_bound a _ N h hc
  rw [← powerCokernelReconstruction_comp_modulePowerHolimIso a M K hK]
  infer_instance

end SerrePositivity.DerivedCompletion
