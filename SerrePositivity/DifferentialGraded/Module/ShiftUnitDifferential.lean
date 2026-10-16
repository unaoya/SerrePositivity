module
public import SerrePositivity.DifferentialGraded.Module.ShiftUnitRelations

/-! # shift包含の閉性 -/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleShiftInElement_d (s : ℤ) (M : RightModule A D) :
    (moduleHom A D M (shiftModule s M)).d (-s) (-s + 1) (moduleShiftInElement A D s M) = 0 := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomElement_d_π, moduleShiftInElement_π, map_zero, δ_units_smul,
    Cochain.δ_rightShift _ s (-s) (-s + 1) (neg_add_cancel s) 1 (by omega)]
  simp only [δ_ofHom, Cochain.rightShift_zero, smul_zero]

end SerrePositivity.DifferentialGraded
