module

public import SerrePositivity.CommutativeAlgebra.Koszul

/-! # Standard degreewise coordinates of a one-element Koszul complex -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R]

namespace Adams

abbrev oneKoszulComplex (a : R) := koszulComplex (fun _ : Fin 1 => a)
abbrev oneKoszulUnit : CochainComplex (ModuleCat.{u} R) ℤ :=
  (HomologicalComplex.single (ModuleCat.{u} R) (.up ℤ) 0).obj (ModuleCat.of R R)


abbrev oneKoszulUnitSelfIso : (oneKoszulUnit (R := R)).X 0 ≅ ModuleCat.of R R :=
  singleObjXSelf (.up ℤ) 0 (ModuleCat.of R R)

abbrev oneKoszulScalarMap (a : R) := smulId a (oneKoszulUnit (R := R))

def oneKoszulXZeroIso (a : R) : (oneKoszulComplex a).X 0 ≅ ModuleCat.of R R where
  hom := (CochainComplex.mappingCone.snd (oneKoszulScalarMap a)).v 0 0 (by omega) ≫
    (oneKoszulUnitSelfIso (R := R)).hom
  inv := (oneKoszulUnitSelfIso (R := R)).inv ≫
    (CochainComplex.mappingCone.inr (oneKoszulScalarMap a)).f 0
  hom_inv_id := by
    apply CochainComplex.mappingCone.ext_from (oneKoszulScalarMap a) 1 0 rfl
    · exact (isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R R) 1 (by decide)).eq_of_src _ _
    · simp only [assoc, Iso.hom_inv_id_assoc, CochainComplex.mappingCone.inr_f_snd_v_assoc]
      exact (Category.comp_id ((CochainComplex.mappingCone.inr (oneKoszulScalarMap a)).f 0)).symm
  inv_hom_id := by simp [Category.assoc]

def oneKoszulXNegOneIso (a : R) : (oneKoszulComplex a).X (-1) ≅ ModuleCat.of R R where
  hom := (CochainComplex.mappingCone.fst (oneKoszulScalarMap a)).1.v (-1) 0 (by omega) ≫
    (oneKoszulUnitSelfIso (R := R)).hom
  inv := (oneKoszulUnitSelfIso (R := R)).inv ≫
    (CochainComplex.mappingCone.inl (oneKoszulScalarMap a)).v 0 (-1) (by omega)
  hom_inv_id := by
    apply CochainComplex.mappingCone.ext_from (oneKoszulScalarMap a) 0 (-1) (by omega)
    · simp only [Int.reduceNeg, assoc, Iso.hom_inv_id_assoc,
        CochainComplex.mappingCone.inl_v_fst_v_assoc]
      exact (Category.comp_id
        ((CochainComplex.mappingCone.inl (oneKoszulScalarMap a)).v 0 (-1) (by omega))).symm
    · exact (isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R R) (-1) (by decide)).eq_of_src _ _
  inv_hom_id := by simp [Category.assoc]

lemma oneKoszul_isZero_X_other (a : R) (n : ℤ) (hn : n ≠ -1 ∧ n ≠ 0) :
    IsZero ((oneKoszulComplex a).X n) := by
  by_cases h : n < -1
  · exact koszulComplex_isZero_X_of_lt (fun _ : Fin 1 => a) n (by simpa using h)
  · exact koszulComplex_isZero_X_of_pos (fun _ : Fin 1 => a) n (by omega)

lemma oneKoszul_generator_d (a : R) :
    (oneKoszulXNegOneIso a).inv ≫ (oneKoszulComplex a).d (-1) 0 =
      a • (oneKoszulXZeroIso a).inv := by
  dsimp [oneKoszulXNegOneIso, oneKoszulXZeroIso]
  change (oneKoszulUnitSelfIso (R := R)).inv ≫
    (CochainComplex.mappingCone.inl (oneKoszulScalarMap a)).v 0 (-1) (by omega) ≫
    (CochainComplex.mappingCone (oneKoszulScalarMap a)).d (-1) 0 = _
  rw [CochainComplex.mappingCone.inl_v_d (oneKoszulScalarMap a) 0 (-1) 1
    (by omega) (by omega)]
  simp [oneKoszulScalarMap, oneKoszulUnit, smulId, Linear.comp_smul,
    Linear.smul_comp]

end Adams
end SerrePositivity
