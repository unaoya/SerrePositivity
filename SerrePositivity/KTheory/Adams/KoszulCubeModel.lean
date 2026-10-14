module

public import SerrePositivity.KTheory.Adams.KoszulSquareModel
public import SerrePositivity.KTheory.Adams.KoszulTensor
public import SerrePositivity.KTheory.Adams.TensorCube

/-! # A mapping-cone model and finite degreewise coordinates of a Koszul cube -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R]
namespace Adams

abbrev oneKoszulCubeCone (a : R) :=
  CochainComplex.mappingCone (smulId a (tensorSquare (oneKoszulComplex a)))

/-- Reassociate the cube, tensor the scalar cone, then remove the tensor unit. -/
def oneKoszulCubeConeIso (a : R) :
    tensorCube (oneKoszulComplex a) ≅ oneKoszulCubeCone a :=
  cochainTensorAssociator (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a) ≪≫
    cochainTensorConeLeft (oneKoszulScalarMap a) (tensorSquare (oneKoszulComplex a)) ≪≫
    HomologicalComplex.homotopyCofiber.mapArrowIso _ _ (fun j => ⟨j - 1, by simp⟩)
      (Arrow.isoMk (cochainTensorLeftUnitor (tensorSquare (oneKoszulComplex a)))
        (cochainTensorLeftUnitor (tensorSquare (oneKoszulComplex a)))
        (oneKoszulTensorScalar_leftUnitor a (tensorSquare (oneKoszulComplex a))).symm)

abbrev oneKoszulCubeConeXSplit (a : R) (n : ℤ) :
    (oneKoszulCubeCone a).X n ≅
      (tensorSquare (oneKoszulComplex a)).X (n + 1) ⊞ (tensorSquare (oneKoszulComplex a)).X n :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod (smulId a (tensorSquare (oneKoszulComplex a)))
    n (n + 1) rfl

def oneKoszulCubeConeXZeroIso (a : R) :
    (oneKoszulCubeCone a).X 0 ≅ ModuleCat.of R R :=
  oneKoszulCubeConeXSplit a 0 ≪≫
    (isoZeroBiprod (oneKoszulSquare_isZero_X_other a 1 (by omega))).symm ≪≫
    oneKoszulSquareXZeroIso a

def oneKoszulCubeConeXNegOneIso (a : R) :
    (oneKoszulCubeCone a).X (-1) ≅ ModuleCat.of R (R × (R × R)) :=
  oneKoszulCubeConeXSplit a (-1) ≪≫
    biprod.mapIso (oneKoszulSquareXZeroIso a) (oneKoszulSquareXNegOneIso a) ≪≫
    ModuleCat.biprodIsoProd (ModuleCat.of R R) (ModuleCat.of R (R × R))

def oneKoszulCubeConeXNegTwoIso (a : R) :
    (oneKoszulCubeCone a).X (-2) ≅ ModuleCat.of R ((R × R) × R) :=
  oneKoszulCubeConeXSplit a (-2) ≪≫
    biprod.mapIso (oneKoszulSquareXNegOneIso a) (oneKoszulSquareXNegTwoIso a) ≪≫
    ModuleCat.biprodIsoProd (ModuleCat.of R (R × R)) (ModuleCat.of R R)

def oneKoszulCubeConeXNegThreeIso (a : R) :
    (oneKoszulCubeCone a).X (-3) ≅ ModuleCat.of R R :=
  oneKoszulCubeConeXSplit a (-3) ≪≫
    (isoBiprodZero (oneKoszulSquare_isZero_X_other a (-3) (by omega))).symm ≪≫
    oneKoszulSquareXNegTwoIso a

lemma oneKoszulCubeCone_isZero_X_other (a : R) (n : ℤ)
    (hn : n ≠ -3 ∧ n ≠ -2 ∧ n ≠ -1 ∧ n ≠ 0) :
    IsZero ((oneKoszulCubeCone a).X n) := by
  apply (CochainComplex.mappingCone.isZero_X_iff _ n).mpr
  exact ⟨oneKoszulSquare_isZero_X_other a (n + 1) (by omega),
    oneKoszulSquare_isZero_X_other a n (by omega)⟩

def oneKoszulCubeXZeroIso (a : R) :
    (tensorCube (oneKoszulComplex a)).X 0 ≅ ModuleCat.of R R :=
  (HomologicalComplex.eval _ _ 0).mapIso (oneKoszulCubeConeIso a) ≪≫
    oneKoszulCubeConeXZeroIso a

def oneKoszulCubeXNegOneIso (a : R) :
    (tensorCube (oneKoszulComplex a)).X (-1) ≅ ModuleCat.of R (R × (R × R)) :=
  (HomologicalComplex.eval _ _ (-1)).mapIso (oneKoszulCubeConeIso a) ≪≫
    oneKoszulCubeConeXNegOneIso a

def oneKoszulCubeXNegTwoIso (a : R) :
    (tensorCube (oneKoszulComplex a)).X (-2) ≅ ModuleCat.of R ((R × R) × R) :=
  (HomologicalComplex.eval _ _ (-2)).mapIso (oneKoszulCubeConeIso a) ≪≫
    oneKoszulCubeConeXNegTwoIso a

def oneKoszulCubeXNegThreeIso (a : R) :
    (tensorCube (oneKoszulComplex a)).X (-3) ≅ ModuleCat.of R R :=
  (HomologicalComplex.eval _ _ (-3)).mapIso (oneKoszulCubeConeIso a) ≪≫
    oneKoszulCubeConeXNegThreeIso a

lemma oneKoszulCube_isZero_X_other (a : R) (n : ℤ)
    (hn : n ≠ -3 ∧ n ≠ -2 ∧ n ≠ -1 ∧ n ≠ 0) :
    IsZero ((tensorCube (oneKoszulComplex a)).X n) :=
  (oneKoszulCubeCone_isZero_X_other a n hn).of_iso
    ((HomologicalComplex.eval _ _ n).mapIso (oneKoszulCubeConeIso a))

end Adams
end SerrePositivity
