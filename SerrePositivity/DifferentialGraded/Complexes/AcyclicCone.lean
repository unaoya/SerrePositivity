module
public import SerrePositivity.DifferentialGraded.Complexes.HomComplex
public import Mathlib.Algebra.Homology.HomotopyCategory.Acyclic

/-! # 既存の複体 cone による quasiIso の判定 -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex
variable (A : Type u) [CommRing A]

/-- 非有界複体の射は、その標準 mapping cone が acyclic であるとき準同型。 -/
lemma complex_quasiIso_iff_acyclic_cone {P Q : Complex A} (f : P ⟶ Q) :
    QuasiIso f ↔ (mappingCone f).Acyclic := by
  have h : (_root_.HomotopyCategory.subcategoryAcyclic (ModuleCat A)).trW
      ((_root_.HomotopyCategory.quotient (ModuleCat A) (.up ℤ)).map f) ↔
      _root_.HomotopyCategory.subcategoryAcyclic (ModuleCat A)
        ((_root_.HomotopyCategory.quotient (ModuleCat A) (.up ℤ)).obj (mappingCone f)) :=
    (_root_.HomotopyCategory.subcategoryAcyclic (ModuleCat A)).trW_iff_of_distinguished
      (mappingCone.triangleh f) (_root_.HomotopyCategory.mappingCone_triangleh_distinguished f)
  rw [← _root_.HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic,
    _root_.HomotopyCategory.quotient_map_mem_quasiIso_iff,
    HomologicalComplex.mem_quasiIso_iff,
    _root_.HomotopyCategory.quotient_obj_mem_subcategoryAcyclic_iff_acyclic] at h
  exact h

end SerrePositivity.DifferentialGraded
