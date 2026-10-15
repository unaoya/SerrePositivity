module

public import SerrePositivity.PerfectComplex.KoszulTensor
public import SerrePositivity.KTheory.Adams.TensorSquare

/-! # A mapping-cone model for the tensor square of a one-element Koszul complex -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u

namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R]

namespace Adams

abbrev oneKoszulSquareCone (a : R) :=
  CochainComplex.mappingCone (smulId a (oneKoszulComplex a))

/-- The unit comparison intertwines the scalar maps on the tensor and on Koszul. -/
lemma oneKoszulTensorScalar_unitor (a : R) :
    cochainTensorMap (oneKoszulScalarMap a) (𝟙 (oneKoszulComplex a)) ≫
      (cochainTensorLeftUnitor (oneKoszulComplex a)).hom =
    (cochainTensorLeftUnitor (oneKoszulComplex a)).hom ≫
      smulId a (oneKoszulComplex a) :=
  oneKoszulTensorScalar_leftUnitor a (oneKoszulComplex a)

/-- Tensoring the scalar cone and then removing the tensor unit gives a double cone. -/
def oneKoszulSquareConeIso (a : R) :
    tensorSquare (oneKoszulComplex a) ≅ oneKoszulSquareCone a :=
  oneKoszulTensorConeIso a (oneKoszulComplex a)

abbrev oneKoszulSquareConeXSplit (a : R) (n : ℤ) :
    (oneKoszulSquareCone a).X n ≅
      (oneKoszulComplex a).X (n + 1) ⊞ (oneKoszulComplex a).X n :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod (smulId a (oneKoszulComplex a))
    n (n + 1) rfl

def oneKoszulSquareConeXZeroIso (a : R) :
    (oneKoszulSquareCone a).X 0 ≅ ModuleCat.of R R :=
  oneKoszulSquareConeXSplit a 0 ≪≫
    (isoZeroBiprod (oneKoszul_isZero_X_other a 1 (by omega))).symm ≪≫
    oneKoszulXZeroIso a

def oneKoszulSquareConeXNegOneIso (a : R) :
    (oneKoszulSquareCone a).X (-1) ≅ ModuleCat.of R (R × R) :=
  oneKoszulSquareConeXSplit a (-1) ≪≫
    biprod.mapIso (oneKoszulXZeroIso a) (oneKoszulXNegOneIso a) ≪≫
    ModuleCat.biprodIsoProd (ModuleCat.of R R) (ModuleCat.of R R)

def oneKoszulSquareConeXNegTwoIso (a : R) :
    (oneKoszulSquareCone a).X (-2) ≅ ModuleCat.of R R :=
  oneKoszulSquareConeXSplit a (-2) ≪≫
    (isoBiprodZero (oneKoszul_isZero_X_other a (-2) (by omega))).symm ≪≫
    oneKoszulXNegOneIso a

lemma oneKoszulSquareCone_isZero_X_other (a : R) (n : ℤ)
    (hn : n ≠ -2 ∧ n ≠ -1 ∧ n ≠ 0) : IsZero ((oneKoszulSquareCone a).X n) := by
  apply (CochainComplex.mappingCone.isZero_X_iff _ n).mpr
  exact ⟨oneKoszul_isZero_X_other a (n + 1) (by omega),
    oneKoszul_isZero_X_other a n (by omega)⟩

def oneKoszulSquareXZeroIso (a : R) :
    (tensorSquare (oneKoszulComplex a)).X 0 ≅ ModuleCat.of R R :=
  (HomologicalComplex.eval _ _ 0).mapIso (oneKoszulSquareConeIso a) ≪≫
    oneKoszulSquareConeXZeroIso a

def oneKoszulSquareXNegOneIso (a : R) :
    (tensorSquare (oneKoszulComplex a)).X (-1) ≅ ModuleCat.of R (R × R) :=
  (HomologicalComplex.eval _ _ (-1)).mapIso (oneKoszulSquareConeIso a) ≪≫
    oneKoszulSquareConeXNegOneIso a

def oneKoszulSquareXNegTwoIso (a : R) :
    (tensorSquare (oneKoszulComplex a)).X (-2) ≅ ModuleCat.of R R :=
  (HomologicalComplex.eval _ _ (-2)).mapIso (oneKoszulSquareConeIso a) ≪≫
    oneKoszulSquareConeXNegTwoIso a

lemma oneKoszulSquare_isZero_X_other (a : R) (n : ℤ)
    (hn : n ≠ -2 ∧ n ≠ -1 ∧ n ≠ 0) :
    IsZero ((tensorSquare (oneKoszulComplex a)).X n) :=
  (oneKoszulSquareCone_isZero_X_other a n hn).of_iso
    ((HomologicalComplex.eval _ _ n).mapIso (oneKoszulSquareConeIso a))

abbrev oneKoszulSquareConeBottom (a : R) :
    ModuleCat.of R R ⟶ (oneKoszulSquareCone a).X 0 :=
  (oneKoszulXZeroIso a).inv ≫ (CochainComplex.mappingCone.inr
    (smulId a (oneKoszulComplex a))).f 0

abbrev oneKoszulSquareConeLeft (a : R) :
    ModuleCat.of R R ⟶ (oneKoszulSquareCone a).X (-1) :=
  (oneKoszulXZeroIso a).inv ≫ (CochainComplex.mappingCone.inl
    (smulId a (oneKoszulComplex a))).v 0 (-1) (by omega)

abbrev oneKoszulSquareConeRight (a : R) :
    ModuleCat.of R R ⟶ (oneKoszulSquareCone a).X (-1) :=
  (oneKoszulXNegOneIso a).inv ≫ (CochainComplex.mappingCone.inr
    (smulId a (oneKoszulComplex a))).f (-1)

abbrev oneKoszulSquareConeTop (a : R) :
    ModuleCat.of R R ⟶ (oneKoszulSquareCone a).X (-2) :=
  (oneKoszulXNegOneIso a).inv ≫ (CochainComplex.mappingCone.inl
    (smulId a (oneKoszulComplex a))).v (-1) (-2) (by omega)

lemma oneKoszulSquareConeLeft_d (a : R) :
    oneKoszulSquareConeLeft a ≫ (oneKoszulSquareCone a).d (-1) 0 =
      a • oneKoszulSquareConeBottom a := by
  have hd : (oneKoszulComplex a).d 0 1 = 0 :=
    (oneKoszul_isZero_X_other a 1 (by omega)).eq_of_tgt _ _
  change (oneKoszulXZeroIso a).inv ≫
    (CochainComplex.mappingCone.inl (smulId a (oneKoszulComplex a))).v 0 (-1) (by omega) ≫
    (oneKoszulSquareCone a).d (-1) 0 = _
  rw [CochainComplex.mappingCone.inl_v_d (smulId a (oneKoszulComplex a))
    0 (-1) 1 (by omega) (by omega)]
  simp [hd, smulId, oneKoszulSquareConeBottom, Linear.smul_comp, Linear.comp_smul]

lemma oneKoszulSquareConeRight_d (a : R) :
    oneKoszulSquareConeRight a ≫ (oneKoszulSquareCone a).d (-1) 0 =
      a • oneKoszulSquareConeBottom a := by
  change (oneKoszulXNegOneIso a).inv ≫
    (CochainComplex.mappingCone.inr (smulId a (oneKoszulComplex a))).f (-1) ≫
    (oneKoszulSquareCone a).d (-1) 0 = _
  rw [CochainComplex.mappingCone.inr_f_d, ← Category.assoc, oneKoszul_generator_d]
  simp [oneKoszulSquareConeBottom, Linear.smul_comp]

lemma oneKoszulSquareConeTop_d (a : R) :
    oneKoszulSquareConeTop a ≫ (oneKoszulSquareCone a).d (-2) (-1) =
      a • oneKoszulSquareConeRight a - a • oneKoszulSquareConeLeft a := by
  change (oneKoszulXNegOneIso a).inv ≫
    (CochainComplex.mappingCone.inl (smulId a (oneKoszulComplex a))).v (-1) (-2) (by omega) ≫
    (oneKoszulSquareCone a).d (-2) (-1) = _
  rw [CochainComplex.mappingCone.inl_v_d (smulId a (oneKoszulComplex a))
    (-1) (-2) 0 (by omega) (by omega), Preadditive.comp_sub,
    ← Category.assoc (oneKoszulXNegOneIso a).inv ((oneKoszulComplex a).d (-1) 0),
    oneKoszul_generator_d]
  simp [smulId, oneKoszulSquareConeLeft, oneKoszulSquareConeRight,
    Linear.smul_comp, Linear.comp_smul]

end Adams
end SerrePositivity
