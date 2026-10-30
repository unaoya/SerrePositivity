module

public import SerrePositivity.CommutativeAlgebra.Koszul
public import SerrePositivity.HomologicalAlgebra.Complex.Cone

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

def oneKoszulXZeroIso (a : R) : (oneKoszulComplex a).X 0 ≅ ModuleCat.of R R :=
  DerivedCompletion.moduleConeSndIso (oneKoszulScalarMap a) 0 1 rfl
    (isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R R) 1 (by decide)) ≪≫ oneKoszulUnitSelfIso

def oneKoszulXNegOneIso (a : R) : (oneKoszulComplex a).X (-1) ≅ ModuleCat.of R R :=
  DerivedCompletion.moduleConeFstIso (oneKoszulScalarMap a) (-1) 0 (by decide)
    (isZero_single_obj_X (.up ℤ) 0 (ModuleCat.of R R) (-1) (by decide)) ≪≫ oneKoszulUnitSelfIso

lemma oneKoszul_isZero_X_other (a : R) (n : ℤ) (hn : n ≠ -1 ∧ n ≠ 0) :
    IsZero ((oneKoszulComplex a).X n) := by
  by_cases h : n < -1
  · exact koszulComplex_isZero_X_of_lt (fun _ : Fin 1 => a) n (by simpa using h)
  · exact koszulComplex_isZero_X_of_pos (fun _ : Fin 1 => a) n (by omega)

lemma oneKoszul_generator_d (a : R) :
    (oneKoszulXNegOneIso a).inv ≫ (oneKoszulComplex a).d (-1) 0 =
      a • (oneKoszulXZeroIso a).inv := by
  dsimp [oneKoszulXNegOneIso, oneKoszulXZeroIso,
    DerivedCompletion.moduleConeFstIso, DerivedCompletion.moduleConeSndIso]
  change (oneKoszulUnitSelfIso (R := R)).inv ≫
    (CochainComplex.mappingCone.inl (oneKoszulScalarMap a)).v 0 (-1) (by omega) ≫
    (CochainComplex.mappingCone (oneKoszulScalarMap a)).d (-1) 0 = _
  rw [CochainComplex.mappingCone.inl_v_d (oneKoszulScalarMap a) 0 (-1) 1
    (by omega) (by omega)]
  simp [oneKoszulScalarMap, oneKoszulUnit, smulId, Linear.comp_smul,
    Linear.smul_comp]
  rfl

end Adams
end SerrePositivity
