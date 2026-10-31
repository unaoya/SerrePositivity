module

public import SerrePositivity.KTheory.Adams.KoszulCubeExt
public import SerrePositivity.PerfectComplex.Tensor.Perfect
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Shuffle

/-! # Coordinates dual to the eight homogeneous Koszul cube generators -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct
variable {R : Type u} [CommRing R]
namespace Adams

abbrev oneKoszulCubeScalarCoordinate (a : R) (i j k : ℤ)
    (ei : (oneKoszulComplex a).X i ≅ ModuleCat.of R R)
    (ej : (oneKoszulComplex a).X j ≅ ModuleCat.of R R)
    (ek : (oneKoszulComplex a).X k ≅ ModuleCat.of R R) (n : ℤ) :=
  cochainTensorTripleScalarCoordinate (oneKoszulComplex a) (oneKoszulComplex a)
    (oneKoszulComplex a) i j k ei.hom ej.hom ek.hom n

lemma oneKoszulCubeGenerator_coordinate_match (a : R) (i j k n : ℤ) (h : i + j + k = n)
    (ei : (oneKoszulComplex a).X i ≅ ModuleCat.of R R)
    (ej : (oneKoszulComplex a).X j ≅ ModuleCat.of R R)
    (ek : (oneKoszulComplex a).X k ≅ ModuleCat.of R R) :
    oneKoszulCubeGenerator a i j k n h ei.inv ej.inv ek.inv ≫
      oneKoszulCubeScalarCoordinate a i j k ei ej ek n = 𝟙 (ModuleCat.of R R) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change cochainTensorTripleScalarCoordinate (oneKoszulComplex a) (oneKoszulComplex a)
    (oneKoszulComplex a) i j k ei.hom ej.hom ek.hom n
    ((1 : R) • cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a)
      (oneKoszulComplex a) i j k n h ((ei.inv 1 ⊗ₜ[R] ej.inv 1) ⊗ₜ[R] ek.inv 1)) = 1
  rw [one_smul, cochainTensorTripleScalarCoordinate_apply_match]
  rw [ModuleCat.hom_inv_apply ei 1, ModuleCat.hom_inv_apply ej 1,
    ModuleCat.hom_inv_apply ek 1]
  simp only [one_mul]

lemma oneKoszulCubeGenerator_coordinate_other (a : R) (i₀ j₀ k₀ i j k n : ℤ)
    (h : i + j + k = n)
    (ei : (oneKoszulComplex a).X i₀ ≅ ModuleCat.of R R)
    (ej : (oneKoszulComplex a).X j₀ ≅ ModuleCat.of R R)
    (ek : (oneKoszulComplex a).X k₀ ≅ ModuleCat.of R R)
    (f : ModuleCat.of R R ⟶ (oneKoszulComplex a).X i)
    (g : ModuleCat.of R R ⟶ (oneKoszulComplex a).X j)
    (e : ModuleCat.of R R ⟶ (oneKoszulComplex a).X k)
    (hne : i ≠ i₀ ∨ j ≠ j₀ ∨ k ≠ k₀) :
    oneKoszulCubeGenerator a i j k n h f g e ≫
      oneKoszulCubeScalarCoordinate a i₀ j₀ k₀ ei ej ek n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext_ring
  change cochainTensorTripleScalarCoordinate (oneKoszulComplex a) (oneKoszulComplex a)
    (oneKoszulComplex a) i₀ j₀ k₀ ei.hom ej.hom ek.hom n
    ((1 : R) • cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a)
      (oneKoszulComplex a) i j k n h ((f 1 ⊗ₜ[R] g 1) ⊗ₜ[R] e 1)) = 0
  rw [one_smul]
  exact cochainTensorTripleScalarCoordinate_apply_other _ _ _ i₀ j₀ k₀ i j k n h
    ei.hom ej.hom ek.hom hne _ _ _

abbrev oneKoszulCubeBottomCoordinate (a : R) :=
  oneKoszulCubeScalarCoordinate a (0) (0) (0)
    (oneKoszulXZeroIso a) (oneKoszulXZeroIso a) (oneKoszulXZeroIso a) (0)

abbrev oneKoszulCubeE0Coordinate (a : R) :=
  oneKoszulCubeScalarCoordinate a (-1) (0) (0)
    (oneKoszulXNegOneIso a) (oneKoszulXZeroIso a) (oneKoszulXZeroIso a) (-1)

abbrev oneKoszulCubeE1Coordinate (a : R) :=
  oneKoszulCubeScalarCoordinate a (0) (-1) (0)
    (oneKoszulXZeroIso a) (oneKoszulXNegOneIso a) (oneKoszulXZeroIso a) (-1)

abbrev oneKoszulCubeE2Coordinate (a : R) :=
  oneKoszulCubeScalarCoordinate a (0) (0) (-1)
    (oneKoszulXZeroIso a) (oneKoszulXZeroIso a) (oneKoszulXNegOneIso a) (-1)

abbrev oneKoszulCubeE01Coordinate (a : R) :=
  oneKoszulCubeScalarCoordinate a (-1) (-1) (0)
    (oneKoszulXNegOneIso a) (oneKoszulXNegOneIso a) (oneKoszulXZeroIso a) (-2)

abbrev oneKoszulCubeE02Coordinate (a : R) :=
  oneKoszulCubeScalarCoordinate a (-1) (0) (-1)
    (oneKoszulXNegOneIso a) (oneKoszulXZeroIso a) (oneKoszulXNegOneIso a) (-2)

abbrev oneKoszulCubeE12Coordinate (a : R) :=
  oneKoszulCubeScalarCoordinate a (0) (-1) (-1)
    (oneKoszulXZeroIso a) (oneKoszulXNegOneIso a) (oneKoszulXNegOneIso a) (-2)

abbrev oneKoszulCubeTopCoordinate (a : R) :=
  oneKoszulCubeScalarCoordinate a (-1) (-1) (-1)
    (oneKoszulXNegOneIso a) (oneKoszulXNegOneIso a) (oneKoszulXNegOneIso a) (-3)

@[reassoc (attr := simp)]
lemma oneKoszulCubeBottom_BottomCoordinate (a : R) :
    oneKoszulCubeBottom a ≫ oneKoszulCubeBottomCoordinate a = 𝟙 _ :=
  oneKoszulCubeGenerator_coordinate_match a (0) (0) (0) (0) (by omega)
    (oneKoszulXZeroIso a) (oneKoszulXZeroIso a) (oneKoszulXZeroIso a)

@[reassoc (attr := simp)]
lemma oneKoszulCubeE0_E0Coordinate (a : R) :
    oneKoszulCubeE0 a ≫ oneKoszulCubeE0Coordinate a = 𝟙 _ :=
  oneKoszulCubeGenerator_coordinate_match a (-1) (0) (0) (-1) (by omega)
    (oneKoszulXNegOneIso a) (oneKoszulXZeroIso a) (oneKoszulXZeroIso a)

@[reassoc (attr := simp)]
lemma oneKoszulCubeE0_E1Coordinate (a : R) :
    oneKoszulCubeE0 a ≫ oneKoszulCubeE1Coordinate a = 0 :=
  oneKoszulCubeGenerator_coordinate_other a (0) (-1) (0) (-1) (0) (0) (-1) (by omega)
    (oneKoszulXZeroIso a) (oneKoszulXNegOneIso a) (oneKoszulXZeroIso a)
    (oneKoszulXNegOneIso a).inv (oneKoszulXZeroIso a).inv (oneKoszulXZeroIso a).inv (by decide)

@[reassoc (attr := simp)]
lemma oneKoszulCubeE0_E2Coordinate (a : R) :
    oneKoszulCubeE0 a ≫ oneKoszulCubeE2Coordinate a = 0 :=
  oneKoszulCubeGenerator_coordinate_other a (0) (0) (-1) (-1) (0) (0) (-1) (by omega)
    (oneKoszulXZeroIso a) (oneKoszulXZeroIso a) (oneKoszulXNegOneIso a)
    (oneKoszulXNegOneIso a).inv (oneKoszulXZeroIso a).inv (oneKoszulXZeroIso a).inv (by decide)

@[reassoc (attr := simp)]
lemma oneKoszulCubeE1_E0Coordinate (a : R) :
    oneKoszulCubeE1 a ≫ oneKoszulCubeE0Coordinate a = 0 :=
  oneKoszulCubeGenerator_coordinate_other a (-1) (0) (0) (0) (-1) (0) (-1) (by omega)
    (oneKoszulXNegOneIso a) (oneKoszulXZeroIso a) (oneKoszulXZeroIso a)
    (oneKoszulXZeroIso a).inv (oneKoszulXNegOneIso a).inv (oneKoszulXZeroIso a).inv (by decide)

@[reassoc (attr := simp)]
lemma oneKoszulCubeE1_E1Coordinate (a : R) :
    oneKoszulCubeE1 a ≫ oneKoszulCubeE1Coordinate a = 𝟙 _ :=
  oneKoszulCubeGenerator_coordinate_match a (0) (-1) (0) (-1) (by omega)
    (oneKoszulXZeroIso a) (oneKoszulXNegOneIso a) (oneKoszulXZeroIso a)

@[reassoc (attr := simp)]
lemma oneKoszulCubeE1_E2Coordinate (a : R) :
    oneKoszulCubeE1 a ≫ oneKoszulCubeE2Coordinate a = 0 :=
  oneKoszulCubeGenerator_coordinate_other a (0) (0) (-1) (0) (-1) (0) (-1) (by omega)
    (oneKoszulXZeroIso a) (oneKoszulXZeroIso a) (oneKoszulXNegOneIso a)
    (oneKoszulXZeroIso a).inv (oneKoszulXNegOneIso a).inv (oneKoszulXZeroIso a).inv (by decide)

@[reassoc (attr := simp)]
lemma oneKoszulCubeE2_E0Coordinate (a : R) :
    oneKoszulCubeE2 a ≫ oneKoszulCubeE0Coordinate a = 0 :=
  oneKoszulCubeGenerator_coordinate_other a (-1) (0) (0) (0) (0) (-1) (-1) (by omega)
    (oneKoszulXNegOneIso a) (oneKoszulXZeroIso a) (oneKoszulXZeroIso a)
    (oneKoszulXZeroIso a).inv (oneKoszulXZeroIso a).inv (oneKoszulXNegOneIso a).inv (by decide)

@[reassoc (attr := simp)]
lemma oneKoszulCubeE2_E1Coordinate (a : R) :
    oneKoszulCubeE2 a ≫ oneKoszulCubeE1Coordinate a = 0 :=
  oneKoszulCubeGenerator_coordinate_other a (0) (-1) (0) (0) (0) (-1) (-1) (by omega)
    (oneKoszulXZeroIso a) (oneKoszulXNegOneIso a) (oneKoszulXZeroIso a)
    (oneKoszulXZeroIso a).inv (oneKoszulXZeroIso a).inv (oneKoszulXNegOneIso a).inv (by decide)

@[reassoc (attr := simp)]
lemma oneKoszulCubeE2_E2Coordinate (a : R) :
    oneKoszulCubeE2 a ≫ oneKoszulCubeE2Coordinate a = 𝟙 _ :=
  oneKoszulCubeGenerator_coordinate_match a (0) (0) (-1) (-1) (by omega)
    (oneKoszulXZeroIso a) (oneKoszulXZeroIso a) (oneKoszulXNegOneIso a)

@[reassoc (attr := simp)]
lemma oneKoszulCubeE01_E01Coordinate (a : R) :
    oneKoszulCubeE01 a ≫ oneKoszulCubeE01Coordinate a = 𝟙 _ :=
  oneKoszulCubeGenerator_coordinate_match a (-1) (-1) (0) (-2) (by omega)
    (oneKoszulXNegOneIso a) (oneKoszulXNegOneIso a) (oneKoszulXZeroIso a)

@[reassoc (attr := simp)]
lemma oneKoszulCubeE01_E02Coordinate (a : R) :
    oneKoszulCubeE01 a ≫ oneKoszulCubeE02Coordinate a = 0 :=
  oneKoszulCubeGenerator_coordinate_other a (-1) (0) (-1) (-1) (-1) (0) (-2) (by omega)
    (oneKoszulXNegOneIso a) (oneKoszulXZeroIso a) (oneKoszulXNegOneIso a)
    (oneKoszulXNegOneIso a).inv (oneKoszulXNegOneIso a).inv (oneKoszulXZeroIso a).inv (by decide)

@[reassoc (attr := simp)]
lemma oneKoszulCubeE01_E12Coordinate (a : R) :
    oneKoszulCubeE01 a ≫ oneKoszulCubeE12Coordinate a = 0 :=
  oneKoszulCubeGenerator_coordinate_other a (0) (-1) (-1) (-1) (-1) (0) (-2) (by omega)
    (oneKoszulXZeroIso a) (oneKoszulXNegOneIso a) (oneKoszulXNegOneIso a)
    (oneKoszulXNegOneIso a).inv (oneKoszulXNegOneIso a).inv (oneKoszulXZeroIso a).inv (by decide)

@[reassoc (attr := simp)]
lemma oneKoszulCubeE02_E01Coordinate (a : R) :
    oneKoszulCubeE02 a ≫ oneKoszulCubeE01Coordinate a = 0 :=
  oneKoszulCubeGenerator_coordinate_other a (-1) (-1) (0) (-1) (0) (-1) (-2) (by omega)
    (oneKoszulXNegOneIso a) (oneKoszulXNegOneIso a) (oneKoszulXZeroIso a)
    (oneKoszulXNegOneIso a).inv (oneKoszulXZeroIso a).inv (oneKoszulXNegOneIso a).inv (by decide)

@[reassoc (attr := simp)]
lemma oneKoszulCubeE02_E02Coordinate (a : R) :
    oneKoszulCubeE02 a ≫ oneKoszulCubeE02Coordinate a = 𝟙 _ :=
  oneKoszulCubeGenerator_coordinate_match a (-1) (0) (-1) (-2) (by omega)
    (oneKoszulXNegOneIso a) (oneKoszulXZeroIso a) (oneKoszulXNegOneIso a)

@[reassoc (attr := simp)]
lemma oneKoszulCubeE02_E12Coordinate (a : R) :
    oneKoszulCubeE02 a ≫ oneKoszulCubeE12Coordinate a = 0 :=
  oneKoszulCubeGenerator_coordinate_other a (0) (-1) (-1) (-1) (0) (-1) (-2) (by omega)
    (oneKoszulXZeroIso a) (oneKoszulXNegOneIso a) (oneKoszulXNegOneIso a)
    (oneKoszulXNegOneIso a).inv (oneKoszulXZeroIso a).inv (oneKoszulXNegOneIso a).inv (by decide)

@[reassoc (attr := simp)]
lemma oneKoszulCubeE12_E01Coordinate (a : R) :
    oneKoszulCubeE12 a ≫ oneKoszulCubeE01Coordinate a = 0 :=
  oneKoszulCubeGenerator_coordinate_other a (-1) (-1) (0) (0) (-1) (-1) (-2) (by omega)
    (oneKoszulXNegOneIso a) (oneKoszulXNegOneIso a) (oneKoszulXZeroIso a)
    (oneKoszulXZeroIso a).inv (oneKoszulXNegOneIso a).inv (oneKoszulXNegOneIso a).inv (by decide)

@[reassoc (attr := simp)]
lemma oneKoszulCubeE12_E02Coordinate (a : R) :
    oneKoszulCubeE12 a ≫ oneKoszulCubeE02Coordinate a = 0 :=
  oneKoszulCubeGenerator_coordinate_other a (-1) (0) (-1) (0) (-1) (-1) (-2) (by omega)
    (oneKoszulXNegOneIso a) (oneKoszulXZeroIso a) (oneKoszulXNegOneIso a)
    (oneKoszulXZeroIso a).inv (oneKoszulXNegOneIso a).inv (oneKoszulXNegOneIso a).inv (by decide)

@[reassoc (attr := simp)]
lemma oneKoszulCubeE12_E12Coordinate (a : R) :
    oneKoszulCubeE12 a ≫ oneKoszulCubeE12Coordinate a = 𝟙 _ :=
  oneKoszulCubeGenerator_coordinate_match a (0) (-1) (-1) (-2) (by omega)
    (oneKoszulXZeroIso a) (oneKoszulXNegOneIso a) (oneKoszulXNegOneIso a)

@[reassoc (attr := simp)]
lemma oneKoszulCubeTop_TopCoordinate (a : R) :
    oneKoszulCubeTop a ≫ oneKoszulCubeTopCoordinate a = 𝟙 _ :=
  oneKoszulCubeGenerator_coordinate_match a (-1) (-1) (-1) (-3) (by omega)
    (oneKoszulXNegOneIso a) (oneKoszulXNegOneIso a) (oneKoszulXNegOneIso a)

end Adams
end SerrePositivity
