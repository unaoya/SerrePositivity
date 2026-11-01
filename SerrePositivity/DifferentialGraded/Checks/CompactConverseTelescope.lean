module
public import SerrePositivity.DifferentialGraded.Perfect.Compact.FiniteGeneration

/-! # compact telescope の有限段階因子分解の公理監査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory Limits Pretriangulated
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (F : ℕ → DerivedModuleCategory A D) (d : ∀ n, F n ⟶ F (n + 1))
    {X : DerivedModuleCategory A D} (hX : moduleCompact A D X)
    (c : (∐ moduleTelescopeFamily A D F) ⟶ X)
    (b : X ⟶ (∐ moduleTelescopeFamily A D F)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk (moduleTelescopeMap A D F d) c b ∈
      distTriang (DerivedModuleCategory A D)) :
    ∃ n : ℕ, Nonempty (Retract X (F n)) :=
  moduleCompact_telescope_retract A D F d hX c b hT

#print axioms moduleCompact_hom_ext_zero
#print axioms moduleTelescopeShift_projection_zero
#print axioms moduleTelescopeShift_projection_succ
#print axioms moduleCompact_telescopeMap_zero
#print axioms moduleCompact_shiftedTelescopeMap_zero
#print axioms moduleCompact_telescope_finite_lift
#print axioms moduleCompact_telescope_factor
#print axioms moduleCompact_telescope_retract
