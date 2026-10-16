module
public import SerrePositivity.DifferentialGraded.Module.ShiftUnitElements

/-! # shiftの包含・射影の通常順合成 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma moduleShiftOutIn (s : ℤ) (M : RightModule A D) :
    compose A (moduleShiftInElement A D s M) (moduleShiftOutElement A D s M)
        (add_neg_cancel s) = (unitElement A (shiftModule s M)).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomCompose_π, moduleShiftOutElement_π, moduleShiftInElement_π, yoneda_moduleUnit_π]
  apply Cochain.ext₀
  intro i
  rw [Cochain.comp_v _ _ _ i (i + s) i rfl (by omega), Cochain.units_smul_v,
    Cochain.leftShift_v _ s s (zero_add s) i (i + s) rfl (i + s) (add_zero _),
    Cochain.rightShift_v _ s (-s) (neg_add_cancel s) (i + s) i (by omega) (i + s) (add_zero _)]
  simp only [Cochain.ofHom_v, HomologicalComplex.id_f,
    CochainComplex.shiftFunctorObjXIso, HomologicalComplex.XIsoOfEq_rfl,
    Iso.refl_hom, Iso.refl_inv, Category.comp_id,
    Linear.comp_units_smul, smul_smul, Int.units_mul_self, one_smul]
  rfl

lemma moduleShiftInOut (s : ℤ) (M : RightModule A D) :
    compose A (moduleShiftOutElement A D s M) (moduleShiftInElement A D s M)
        (neg_add_cancel s) = (unitElement A M).val := by
  apply moduleHomElement_ext A D
  intro x
  rw [moduleHomCompose_π, moduleShiftInElement_π, moduleShiftOutElement_π, yoneda_moduleUnit_π]
  apply Cochain.ext₀
  intro i
  rw [Cochain.comp_v _ _ _ i (i - s) i (by omega) (by omega), Cochain.units_smul_v,
    Cochain.rightShift_v _ s (-s) (neg_add_cancel s) i (i - s) (by omega) i (add_zero _),
    Cochain.leftShift_v _ s s (zero_add s) (i - s) i (by omega) i (add_zero _)]
  simp only [Cochain.ofHom_v, HomologicalComplex.id_f,
    CochainComplex.shiftFunctorObjXIso, Category.id_comp, Category.comp_id,
    Linear.units_smul_comp, Linear.comp_units_smul, smul_smul, Int.units_mul_self, one_smul]
  exact (XIsoOfEq (M.obj (op x)) (show i - s + s = i by omega)).inv_hom_id

end SerrePositivity.DifferentialGraded
