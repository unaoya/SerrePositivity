module
public import SerrePositivity.HomologicalAlgebra.ConeLES
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # Acyclicity and mapping cones of module cochain complexes -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Limits HomologicalComplex CochainComplex
variable {R : Type u} [CommRing R]

lemma cochainAcyclic_of_iso {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (hP : P.Acyclic) (e : P ≅ Q) : Q.Acyclic :=
  fun i => (hP i).of_iso e

lemma cochainAcyclic_of_homotopyEquiv {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (hP : P.Acyclic) (e : HomotopyEquiv P Q) : Q.Acyclic := by
  intro i
  exact (exactAt_iff_isZero_homology Q i).mpr
    ((e.toHomologyIso i).isZero_iff.mp (hP i).isZero_homology)

lemma cochainAcyclic_shift {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (hP : P.Acyclic) (n : ℤ) : (P⟦n⟧).Acyclic := by
  intro i
  exact (exactAt_iff_isZero_homology _ i).mpr
    (((CochainComplex.ShiftSequence.shiftIso
      (ModuleCat.{u} R) n i (n + i) rfl).app P).isZero_iff.mpr
      (hP (n + i)).isZero_homology)

lemma cochainAcyclic_of_shift {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (n : ℤ) (hP : (P⟦n⟧).Acyclic) : P.Acyclic :=
  cochainAcyclic_of_iso (cochainAcyclic_shift hP (-n)) (shiftShiftNeg P n)

lemma cochainAcyclic_mappingCone {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : P ⟶ Q) (hP : P.Acyclic) (hQ : Q.Acyclic) : (mappingCone f).Acyclic := by
  intro i
  exact (exactAt_iff_isZero_homology _ i).mpr
    ((Cone.exact₃ f i (i + 1) rfl).isZero_of_both_isZero
      (hQ i).isZero_homology (hP (i + 1)).isZero_homology)

/-- A cochain map is a quasi-isomorphism precisely when its concrete cone is acyclic. -/
lemma cochain_quasiIso_iff_cone_acyclic
    {P P' : CochainComplex (ModuleCat.{u} R) ℤ} (f : P ⟶ P') :
    QuasiIso f ↔ (CochainComplex.mappingCone f).Acyclic := by
  rw [← HomologicalComplex.mem_quasiIso_iff,
    ← HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
  exact ((HomotopyCategory.subcategoryAcyclic (ModuleCat.{u} R)).trW_iff_of_distinguished
    (CochainComplex.mappingCone.triangleh f)
    (HomotopyCategory.mappingCone_triangleh_distinguished f)).trans
      (HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic _)

end SerrePositivity
