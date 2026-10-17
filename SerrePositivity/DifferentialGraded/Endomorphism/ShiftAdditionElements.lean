module
public import SerrePositivity.DifferentialGraded.Endomorphism.ShiftZeroCoherence

/-! # 正規化斉次射影と加法shiftの合成 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]

lemma normalizedModuleShiftOut_v_eq (s : ℤ) (M : RightModule A D) (x : D)
    (i j : ℤ) (hij : i + s = j) :
    ((moduleHomπ A D (shiftModule s M) M x).f s (normalizedModuleShiftOut A D s M)).v
        i j hij = ((M.obj (op x)).XIsoOfEq hij).hom := by
  rw [← Cochain.v_comp_XIsoOfEq_hom _ i (i + s) j rfl hij,
    normalizedModuleShiftOut_v, Category.id_comp]

lemma normalizedModuleShiftOut_add (s t : ℤ) (M : RightModule A D) :
    forward A (x := shiftModule (s + t) M) (y := shiftModule t (shiftModule s M)) (z := M)
      (endomorphismClosedElement A D (moduleShiftAddIsoObj A D s t M).hom)
      (compose A (x := shiftModule t (shiftModule s M)) (y := shiftModule s M) (z := M)
        (normalizedModuleShiftOut A D s M)
        (normalizedModuleShiftOut A D t (shiftModule s M)) (add_comm t s))
      (zero_add (s + t)) = normalizedModuleShiftOut A D (s + t) M := by
  apply moduleHomElement_ext A D
  intro x
  have hπ : (moduleHomπ A D (shiftModule (s + t) M) (shiftModule t (shiftModule s M)) x).f 0
      (endomorphismClosedElement A D (moduleShiftAddIsoObj A D s t M).hom) =
      Cochain.ofHom ((moduleEvaluation A D x).map (moduleShiftAddIsoObj A D s t M).hom) :=
    endomorphismClosedElement_π A D (moduleShiftAddIsoObj A D s t M).hom x
  rw [moduleHomForward_π]
  simp only [zero_mul, Int.negOnePow_zero, one_smul]
  erw [hπ]
  simp only [compose, Units.smul_def, map_zsmul]
  rw [moduleHomForward_π]
  simp only [← Units.smul_def, smul_smul, Int.units_mul_self, one_smul]
  apply Cochain.ext
  intro i j hij
  rw [Cochain.zero_cochain_comp_v,
    Cochain.comp_v _ _ _ i (i + t) j rfl (by omega),
    normalizedModuleShiftOut_v, normalizedModuleShiftOut_v_eq,
    normalizedModuleShiftOut_v_eq, Cochain.ofHom_v, moduleShiftAddIsoObj_hom_eval,
    shiftFunctorAdd_hom_app_f, Category.id_comp]
  change ((M.obj (op x)).XIsoOfEq _).hom ≫ ((M.obj (op x)).XIsoOfEq _).hom =
    ((M.obj (op x)).XIsoOfEq _).hom
  simp only [XIsoOfEq, eqToIso.hom, eqToHom_trans]

end SerrePositivity.DifferentialGraded
