module
public import SerrePositivity.DifferentialGraded.Perfect.UniversalProperty
public import SerrePositivity.DifferentialGraded.Perfect.Generators

/-! # finite cellとPerfの最小性の検査 -/
@[expose] public section
noncomputable section
universe u v
open CategoryTheory
open SerrePositivity.DifferentialGraded
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

example (S : Set D) (P : ObjectProperty (DerivedModuleCategory A D))
    [P.IsTriangulated] [P.IsStableUnderRetracts]
    (h : ∀ x ∈ S, P ((moduleToDerived A D).obj
      (ForgetEnrichment.of (Complex A) (representable A x)))) : modulePerfectOver A D S ≤ P :=
  modulePerfectOver_le_of_generators A D P S h

example : modulePerfect A D ≤ moduleCompact A D := by
  rw [modulePerfect_le_iff_generators]
  exact moduleRepresentable_compact A D

example (S : Set D) : derivedFiniteCellOver A D S ≤ modulePerfectOver A D S :=
  (derivedFiniteCellOver A D S).le_retractClosure

#print axioms moduleDerivedBiprod_mem_triangulated
#print axioms ModuleFiniteCellCode.mem_triangulated
#print axioms derivedFiniteCellOver_le_iff_generators
#print axioms modulePerfectOver_le_of_generators
#print axioms modulePerfectOver_le_iff_generators
#print axioms modulePerfect_le_iff_generators
