module
public import SerrePositivity.HomologicalAlgebra.ExtZeroComparison
public import SerrePositivity.HomologicalAlgebra.KoszulDualZeroTorsion

/-! # Actual Mathlib local cohomology in degree zero is ideal-power torsion -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory CategoryTheory.Limits Opposite HomologicalComplex
variable {R : Type u} [CommRing R] [IsNoetherian R R] {e : ℕ} (z : Fin e → R)

/-- Mathlib's Ext-colimit local cohomology in degree zero is the actual power-torsion functor,
naturally in all coefficients and their morphisms. -/
def localCohomologyZeroPowerTorsionNatIso :
    localCohomology (Ideal.span (Set.range z)) 0 ≅
      idealPowerTorsionFunctor (Ideal.span (Set.range z)) :=
  (localCohomologyPowerKoszulIdealNatIso z 0).symm ≪≫
    (Functor.Final.colimitIso (opOp ℕ)
      (localCohomology.diagram (powerKoszulIdealDiagram z) 0)).symm ≪≫
    HasColimit.isoOfNatIso (Functor.isoWhiskerLeft
      (opOp ℕ ⋙ (localCohomology.ringModIdeals (powerKoszulIdealDiagram z)).op)
      extZeroLinearCoyonedaNatIso) ≪≫ quotientHomColimitPowerTorsionNatIso z

/-- The actual zero dual-colimit cohomology agrees with Mathlib's actual zero local cohomology. -/
def koszulDualColimitZeroLocalCohomologyNatIso :
    koszulDualColimitFunctor z ⋙ homologyFunctor (ModuleCat.{u} R) (.up ℕ) 0 ≅
      localCohomology (Ideal.span (Set.range z)) 0 :=
  koszulDualColimitZeroTorsionNatIso z ≪≫ (localCohomologyZeroPowerTorsionNatIso z).symm

end SerrePositivity
