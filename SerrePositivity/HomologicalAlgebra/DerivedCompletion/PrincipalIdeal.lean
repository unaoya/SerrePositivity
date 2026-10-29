module

public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrincipalQuotientComplete
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.FinitePresentationComplete

/-! # Derived completeness of a principal ideal

The ideal is the kernel of the actual quotient map. Its generator need not be
regular, and neither bounded torsion nor classical completeness is assumed.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.DerivedCompletion

/-- A principal ideal of a derived complete ring is derived complete as a module. -/
theorem isModuleComplete_principal_ideal
    (R : Type u) [CommRing R] (f d : R)
    (hR : IsModuleComplete R f (ModuleCat.of R R)) :
    IsModuleComplete R f (ModuleCat.of R (Ideal.span {d})) := by
  have hquot := isModuleComplete_principal_quotient_restrict R f d hR
  let I : Submodule R R := Ideal.span {d}
  have hker := isModuleComplete_ker R f I.mkQ hR hquot
  change IsModuleComplete R f (ModuleCat.of R I.mkQ.ker) at hker
  rw [Submodule.ker_mkQ] at hker
  exact hker

/-- A finitely presented algebra module over a derived complete base supplies
all three completeness conditions for a principal closed side, including the
original coefficient action and the intrinsic quotient action. -/
theorem isModuleComplete_finitePresentation_algebra_principal
    (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
    [Module.FinitePresentation R A] (f : R) (d : A)
    (hR : IsModuleComplete R f (ModuleCat.of R R)) :
    IsModuleComplete R f (ModuleCat.of R A) ∧
      IsModuleComplete A (algebraMap R A f) (ModuleCat.of A A) ∧
      IsModuleComplete A (algebraMap R A f) (ModuleCat.of A (Ideal.span {d})) ∧
      IsModuleComplete (A ⧸ Ideal.span {d})
        (algebraMap A (A ⧸ Ideal.span {d}) (algebraMap R A f))
        (ModuleCat.of (A ⧸ Ideal.span {d}) (A ⧸ Ideal.span {d})) := by
  have hA := isModuleComplete_of_finitePresentation R f hR (ModuleCat.of R A)
  have hAA := (isModuleComplete_algebraMap_iff R A f A).mpr hA
  exact ⟨hA, hAA, isModuleComplete_principal_ideal A _ d hAA,
    isModuleComplete_principal_quotient A _ d hAA⟩

end SerrePositivity.DerivedCompletion
