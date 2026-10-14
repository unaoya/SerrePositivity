module

public import SerrePositivity.KTheory.Adams.KoszulCubeModel

/-! # Eight homogeneous generators and the signed rotation of a Koszul cube -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
open scoped TensorProduct
variable {R : Type u} [CommRing R]
namespace Adams

def oneKoszulCubeGenerator (a : R) (i j k n : ℤ) (h : i + j + k = n)
    (f : ModuleCat.of R R ⟶ (oneKoszulComplex a).X i)
    (g : ModuleCat.of R R ⟶ (oneKoszulComplex a).X j)
    (e : ModuleCat.of R R ⟶ (oneKoszulComplex a).X k) :
    ModuleCat.of R R ⟶ (tensorCube (oneKoszulComplex a)).X n :=
  ModuleCat.ofHom ((LinearMap.id : R →ₗ[R] R).smulRight
    (cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
      i j k n h ((f 1 ⊗ₜ[R] g 1) ⊗ₜ[R] e 1)))

@[simp]
lemma oneKoszulCubeGenerator_apply (a : R) (i j k n : ℤ) (h : i + j + k = n)
    (f : ModuleCat.of R R ⟶ (oneKoszulComplex a).X i)
    (g : ModuleCat.of R R ⟶ (oneKoszulComplex a).X j)
    (e : ModuleCat.of R R ⟶ (oneKoszulComplex a).X k) (r : R) :
    oneKoszulCubeGenerator a i j k n h f g e r =
      r • cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
        i j k n h ((f 1 ⊗ₜ[R] g 1) ⊗ₜ[R] e 1) := rfl

lemma oneKoszulCubeGenerator_rotation (a : R) (i j k n : ℤ) (h : i + j + k = n)
    (f : ModuleCat.of R R ⟶ (oneKoszulComplex a).X i)
    (g : ModuleCat.of R R ⟶ (oneKoszulComplex a).X j)
    (e : ModuleCat.of R R ⟶ (oneKoszulComplex a).X k) :
    oneKoszulCubeGenerator a i j k n h f g e ≫ (tensorCubeRotation (oneKoszulComplex a)).f n =
      ((i + j) * k).negOnePow • oneKoszulCubeGenerator a k i j n (by omega) e f g := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change (tensorCubeRotation (oneKoszulComplex a)).f n
    (r • cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
      i j k n h ((f 1 ⊗ₜ[R] g 1) ⊗ₜ[R] e 1)) =
    ((i + j) * k).negOnePow •
      (r • cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
        k i j n (by omega) ((e 1 ⊗ₜ[R] f 1) ⊗ₜ[R] g 1))
  rw [map_smul, tensorCubeRotation_apply_ι]
  exact smul_comm r ((i + j) * k).negOnePow _

abbrev oneKoszulCubeBottom (a : R) :=
  oneKoszulCubeGenerator a (0) (0) (0) (0) (by omega)
    (oneKoszulXZeroIso a).inv (oneKoszulXZeroIso a).inv (oneKoszulXZeroIso a).inv

abbrev oneKoszulCubeE0 (a : R) :=
  oneKoszulCubeGenerator a (-1) (0) (0) (-1) (by omega)
    (oneKoszulXNegOneIso a).inv (oneKoszulXZeroIso a).inv (oneKoszulXZeroIso a).inv

abbrev oneKoszulCubeE1 (a : R) :=
  oneKoszulCubeGenerator a (0) (-1) (0) (-1) (by omega)
    (oneKoszulXZeroIso a).inv (oneKoszulXNegOneIso a).inv (oneKoszulXZeroIso a).inv

abbrev oneKoszulCubeE2 (a : R) :=
  oneKoszulCubeGenerator a (0) (0) (-1) (-1) (by omega)
    (oneKoszulXZeroIso a).inv (oneKoszulXZeroIso a).inv (oneKoszulXNegOneIso a).inv

abbrev oneKoszulCubeE01 (a : R) :=
  oneKoszulCubeGenerator a (-1) (-1) (0) (-2) (by omega)
    (oneKoszulXNegOneIso a).inv (oneKoszulXNegOneIso a).inv (oneKoszulXZeroIso a).inv

abbrev oneKoszulCubeE02 (a : R) :=
  oneKoszulCubeGenerator a (-1) (0) (-1) (-2) (by omega)
    (oneKoszulXNegOneIso a).inv (oneKoszulXZeroIso a).inv (oneKoszulXNegOneIso a).inv

abbrev oneKoszulCubeE12 (a : R) :=
  oneKoszulCubeGenerator a (0) (-1) (-1) (-2) (by omega)
    (oneKoszulXZeroIso a).inv (oneKoszulXNegOneIso a).inv (oneKoszulXNegOneIso a).inv

abbrev oneKoszulCubeTop (a : R) :=
  oneKoszulCubeGenerator a (-1) (-1) (-1) (-3) (by omega)
    (oneKoszulXNegOneIso a).inv (oneKoszulXNegOneIso a).inv (oneKoszulXNegOneIso a).inv

lemma oneKoszulCubeBottom_rotation (a : R) :
    oneKoszulCubeBottom a ≫ (tensorCubeRotation (oneKoszulComplex a)).f (0) =
      oneKoszulCubeBottom a := by
  simpa using oneKoszulCubeGenerator_rotation a (0) (0) (0) (0) (by omega)
    (oneKoszulXZeroIso a).inv (oneKoszulXZeroIso a).inv (oneKoszulXZeroIso a).inv

lemma oneKoszulCubeE0_rotation (a : R) :
    oneKoszulCubeE0 a ≫ (tensorCubeRotation (oneKoszulComplex a)).f (-1) =
      oneKoszulCubeE1 a := by
  simpa using oneKoszulCubeGenerator_rotation a (-1) (0) (0) (-1) (by omega)
    (oneKoszulXNegOneIso a).inv (oneKoszulXZeroIso a).inv (oneKoszulXZeroIso a).inv

lemma oneKoszulCubeE1_rotation (a : R) :
    oneKoszulCubeE1 a ≫ (tensorCubeRotation (oneKoszulComplex a)).f (-1) =
      oneKoszulCubeE2 a := by
  simpa using oneKoszulCubeGenerator_rotation a (0) (-1) (0) (-1) (by omega)
    (oneKoszulXZeroIso a).inv (oneKoszulXNegOneIso a).inv (oneKoszulXZeroIso a).inv

lemma oneKoszulCubeE2_rotation (a : R) :
    oneKoszulCubeE2 a ≫ (tensorCubeRotation (oneKoszulComplex a)).f (-1) =
      oneKoszulCubeE0 a := by
  simpa using oneKoszulCubeGenerator_rotation a (0) (0) (-1) (-1) (by omega)
    (oneKoszulXZeroIso a).inv (oneKoszulXZeroIso a).inv (oneKoszulXNegOneIso a).inv

lemma oneKoszulCubeE01_rotation (a : R) :
    oneKoszulCubeE01 a ≫ (tensorCubeRotation (oneKoszulComplex a)).f (-2) =
      oneKoszulCubeE12 a := by
  simpa using oneKoszulCubeGenerator_rotation a (-1) (-1) (0) (-2) (by omega)
    (oneKoszulXNegOneIso a).inv (oneKoszulXNegOneIso a).inv (oneKoszulXZeroIso a).inv

lemma oneKoszulCubeE02_rotation (a : R) :
    oneKoszulCubeE02 a ≫ (tensorCubeRotation (oneKoszulComplex a)).f (-2) =
      -oneKoszulCubeE01 a := by
  simpa using oneKoszulCubeGenerator_rotation a (-1) (0) (-1) (-2) (by omega)
    (oneKoszulXNegOneIso a).inv (oneKoszulXZeroIso a).inv (oneKoszulXNegOneIso a).inv

lemma oneKoszulCubeE12_rotation (a : R) :
    oneKoszulCubeE12 a ≫ (tensorCubeRotation (oneKoszulComplex a)).f (-2) =
      -oneKoszulCubeE02 a := by
  simpa using oneKoszulCubeGenerator_rotation a (0) (-1) (-1) (-2) (by omega)
    (oneKoszulXZeroIso a).inv (oneKoszulXNegOneIso a).inv (oneKoszulXNegOneIso a).inv

lemma oneKoszulCubeTop_rotation (a : R) :
    oneKoszulCubeTop a ≫ (tensorCubeRotation (oneKoszulComplex a)).f (-3) =
      oneKoszulCubeTop a := by
  simpa [show (2 : ℤ).negOnePow = 1 from Int.negOnePow_two_mul 1] using
    oneKoszulCubeGenerator_rotation a (-1) (-1) (-1) (-3) (by omega)
    (oneKoszulXNegOneIso a).inv (oneKoszulXNegOneIso a).inv (oneKoszulXNegOneIso a).inv

end Adams
end SerrePositivity
