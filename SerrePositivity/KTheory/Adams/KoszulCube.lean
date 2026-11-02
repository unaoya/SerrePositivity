module

public import SerrePositivity.KTheory.Adams.KoszulSquare
public import SerrePositivity.PerfectComplex.KoszulTensor
public import SerrePositivity.KTheory.Adams.TensorPower.TensorCube
public import SerrePositivity.PerfectComplex.Tensor.Perfect
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Shuffle
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Cone
public import SerrePositivity.PerfectComplex.RankOneTensorTripleExt

/-! # 一元 Koszul 複体のテンソル三乗

## 概要

一元 Koszul 複体のテンソル三乗の写像錐モデルと次数ごとの有限な座標、八つの同次生成元と符号付きの回転、生成元の上の微分、各次数で写像が生成元で決まること、双対の座標を与える。

## 方針

項を八つの生成元で張り、微分と回転を生成元の上で計算する。

## 規約

`simp` の多い長い証明が集まるので、Fourier の部分と分けている。

## 使われ方

`Adams/KoszulCubeFourier`・`Adams/CyclicThree` の Koszul の正規化。
-/

@[expose] public noncomputable section

universe u

section KoszulCubeModelPart

set_option backward.isDefEq.respectTransparency false
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
    oneKoszulTensorConeIso a (tensorSquare (oneKoszulComplex a))

lemma oneKoszulCubeCone_isZero_X_other (a : R) (n : ℤ)
    (hn : n ≠ -3 ∧ n ≠ -2 ∧ n ≠ -1 ∧ n ≠ 0) :
    IsZero ((oneKoszulCubeCone a).X n) := by
  apply (CochainComplex.mappingCone.isZero_X_iff _ n).mpr
  exact ⟨oneKoszulSquare_isZero_X_other a (n + 1) (by omega),
    oneKoszulSquare_isZero_X_other a n (by omega)⟩

lemma oneKoszulCube_isZero_X_other (a : R) (n : ℤ)
    (hn : n ≠ -3 ∧ n ≠ -2 ∧ n ≠ -1 ∧ n ≠ 0) :
    IsZero ((tensorCube (oneKoszulComplex a)).X n) :=
  (oneKoszulCubeCone_isZero_X_other a n hn).of_iso
    ((HomologicalComplex.eval _ _ n).mapIso (oneKoszulCubeConeIso a))

end Adams
end SerrePositivity

end KoszulCubeModelPart

section KoszulCubeGeneratorsPart

set_option backward.isDefEq.respectTransparency false
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

end KoszulCubeGeneratorsPart

section KoszulCubeDifferentialPart

set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
open scoped TensorProduct
variable {R : Type u} [CommRing R]
namespace Adams

private lemma moduleHom_map_zero {M N : ModuleCat.{u} R} (f : M ⟶ N) :
    f.hom' 0 = 0 := f.hom'.map_zero

lemma oneKoszulXNegOne_generator_d_apply (a : R) (r : R) :
    (oneKoszulComplex a).d (-1) 0 ((oneKoszulXNegOneIso a).inv r) =
      a • (oneKoszulXZeroIso a).inv r :=
  congrArg (fun f => f r) (oneKoszul_generator_d a)

lemma oneKoszulXZero_generator_d_apply (a : R) (r : R) :
    (oneKoszulComplex a).d 0 1 ((oneKoszulXZeroIso a).inv r) = 0 := by
  have he : (oneKoszulXZeroIso a).inv ≫ (oneKoszulComplex a).d 0 1 = 0 :=
    (oneKoszul_isZero_X_other a 1 (by omega)).eq_of_tgt _ _
  exact congrArg (fun f => f r) he

lemma oneKoszulCubeE0_d (a : R) :
    oneKoszulCubeE0 a ≫ (tensorCube (oneKoszulComplex a)).d (-1) (0) =
      a • oneKoszulCubeBottom a := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change (tensorCube (oneKoszulComplex a)).d (-1) (0)
    (r • (cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
      (-1) (0) (0) (-1) (by omega)
      (((oneKoszulXNegOneIso a).inv 1 ⊗ₜ[R] (oneKoszulXZeroIso a).inv 1) ⊗ₜ[R] (oneKoszulXZeroIso
        a).inv 1))) =
    a • (r • (cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
      (0) (0) (0) (0) (by omega)
      (((oneKoszulXZeroIso a).inv 1 ⊗ₜ[R] (oneKoszulXZeroIso a).inv 1) ⊗ₜ[R] (oneKoszulXZeroIso
        a).inv 1)))
  have hd := cochainTensorTriple_d_apply_ι
    (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
      (-1) (0) (0) (-1) (by omega)
      ((oneKoszulXNegOneIso a).inv 1)
      ((oneKoszulXZeroIso a).inv 1)
      ((oneKoszulXZeroIso a).inv 1)
  simp only [Int.reduceAdd, Int.reduceNeg] at hd
  rw [oneKoszulXNegOne_generator_d_apply a 1] at hd
  try rw [oneKoszulXZero_generator_d_apply a 1] at hd
  dsimp only [ConcreteCategory.hom] at hd
  simp only [TensorProduct.zero_tmul, TensorProduct.tmul_zero, moduleHom_map_zero, neg_zero,
    add_zero, Units.smul_def, Int.negOnePow_neg, Int.negOnePow_one, Units.val_neg, Units.val_one,
    neg_one_smul, ← TensorProduct.smul_tmul' (R := R) (R' := R)] at hd
  rw [(cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
    (0) (0) (0) (0) (by omega)).hom'.map_smul a] at hd
  rw [map_smul]
  dsimp only [ConcreteCategory.hom]
  rw [hd]
  module

lemma oneKoszulCubeE1_d (a : R) :
    oneKoszulCubeE1 a ≫ (tensorCube (oneKoszulComplex a)).d (-1) (0) =
      a • oneKoszulCubeBottom a := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change (tensorCube (oneKoszulComplex a)).d (-1) (0)
    (r • (cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
      (0) (-1) (0) (-1) (by omega)
      (((oneKoszulXZeroIso a).inv 1 ⊗ₜ[R] (oneKoszulXNegOneIso a).inv 1) ⊗ₜ[R] (oneKoszulXZeroIso
        a).inv 1))) =
    a • (r • (cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
      (0) (0) (0) (0) (by omega)
      (((oneKoszulXZeroIso a).inv 1 ⊗ₜ[R] (oneKoszulXZeroIso a).inv 1) ⊗ₜ[R] (oneKoszulXZeroIso
        a).inv 1)))
  have hd := cochainTensorTriple_d_apply_ι
    (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
      (0) (-1) (0) (-1) (by omega)
      ((oneKoszulXZeroIso a).inv 1)
      ((oneKoszulXNegOneIso a).inv 1)
      ((oneKoszulXZeroIso a).inv 1)
  simp only [Int.reduceAdd, Int.reduceNeg] at hd
  rw [oneKoszulXNegOne_generator_d_apply a 1] at hd
  try rw [oneKoszulXZero_generator_d_apply a 1] at hd
  dsimp only [ConcreteCategory.hom] at hd
  simp only [TensorProduct.zero_tmul, TensorProduct.tmul_zero, moduleHom_map_zero, neg_zero,
    zero_add, add_zero, Units.smul_def, Int.negOnePow_neg, Int.negOnePow_one, Int.negOnePow_zero,
    Units.val_neg, Units.val_one, one_smul, neg_one_smul, ← TensorProduct.smul_tmul' (R := R) (R'
    := R), TensorProduct.tmul_smul (R := R) (R' := R)] at hd
  rw [(cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
    (0) (0) (0) (0) (by omega)).hom'.map_smul a] at hd
  rw [map_smul]
  dsimp only [ConcreteCategory.hom]
  rw [hd]
  module

lemma oneKoszulCubeE2_d (a : R) :
    oneKoszulCubeE2 a ≫ (tensorCube (oneKoszulComplex a)).d (-1) (0) =
      a • oneKoszulCubeBottom a := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change (tensorCube (oneKoszulComplex a)).d (-1) (0)
    (r • (cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
      (0) (0) (-1) (-1) (by omega)
      (((oneKoszulXZeroIso a).inv 1 ⊗ₜ[R] (oneKoszulXZeroIso a).inv 1) ⊗ₜ[R] (oneKoszulXNegOneIso
        a).inv 1))) =
    a • (r • (cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
      (0) (0) (0) (0) (by omega)
      (((oneKoszulXZeroIso a).inv 1 ⊗ₜ[R] (oneKoszulXZeroIso a).inv 1) ⊗ₜ[R] (oneKoszulXZeroIso
        a).inv 1)))
  have hd := cochainTensorTriple_d_apply_ι
    (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
      (0) (0) (-1) (-1) (by omega)
      ((oneKoszulXZeroIso a).inv 1)
      ((oneKoszulXZeroIso a).inv 1)
      ((oneKoszulXNegOneIso a).inv 1)
  simp only [Int.reduceAdd, Int.reduceNeg] at hd
  rw [oneKoszulXNegOne_generator_d_apply a 1] at hd
  try rw [oneKoszulXZero_generator_d_apply a 1] at hd
  dsimp only [ConcreteCategory.hom] at hd
  simp only [TensorProduct.zero_tmul, TensorProduct.tmul_zero, moduleHom_map_zero, zero_add,
    add_zero, Int.negOnePow_zero, one_smul, TensorProduct.tmul_smul (R := R) (R' := R)] at hd
  rw [(cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
    (0) (0) (0) (0) (by omega)).hom'.map_smul a] at hd
  rw [map_smul]
  dsimp only [ConcreteCategory.hom]
  rw [hd]
  module

lemma oneKoszulCubeE01_d (a : R) :
    oneKoszulCubeE01 a ≫ (tensorCube (oneKoszulComplex a)).d (-2) (-1) =
      a • oneKoszulCubeE1 a - a • oneKoszulCubeE0 a := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change (tensorCube (oneKoszulComplex a)).d (-2) (-1)
    (r • (cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
      (-1) (-1) (0) (-2) (by omega)
      (((oneKoszulXNegOneIso a).inv 1 ⊗ₜ[R] (oneKoszulXNegOneIso a).inv 1) ⊗ₜ[R]
        (oneKoszulXZeroIso a).inv 1))) =
    a • (r • (cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
      (0) (-1) (0) (-1) (by omega)
      (((oneKoszulXZeroIso a).inv 1 ⊗ₜ[R] (oneKoszulXNegOneIso a).inv 1) ⊗ₜ[R] (oneKoszulXZeroIso
        a).inv 1))) -
    a • (r • (cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
      (-1) (0) (0) (-1) (by omega)
      (((oneKoszulXNegOneIso a).inv 1 ⊗ₜ[R] (oneKoszulXZeroIso a).inv 1) ⊗ₜ[R] (oneKoszulXZeroIso
        a).inv 1)))
  have hd := cochainTensorTriple_d_apply_ι
    (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
      (-1) (-1) (0) (-2) (by omega)
      ((oneKoszulXNegOneIso a).inv 1)
      ((oneKoszulXNegOneIso a).inv 1)
      ((oneKoszulXZeroIso a).inv 1)
  simp only [Int.reduceAdd, Int.reduceNeg] at hd
  rw [oneKoszulXNegOne_generator_d_apply a 1] at hd
  try rw [oneKoszulXZero_generator_d_apply a 1] at hd
  dsimp only [ConcreteCategory.hom] at hd
  simp only [TensorProduct.tmul_zero, moduleHom_map_zero, add_zero, Units.smul_def,
    Int.negOnePow_neg, Int.negOnePow_one, show (2 : ℤ).negOnePow = 1 from Int.negOnePow_two_mul 1,
    Units.val_neg, Units.val_one, one_smul, neg_one_smul, ← TensorProduct.smul_tmul' (R := R) (R'
    := R), TensorProduct.tmul_smul (R := R) (R' := R)] at hd
  rw [(cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
    (0) (-1) (0) (-1) (by omega)).hom'.map_smul a] at hd
  rw [(cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
    (-1) (0) (0) (-1) (by omega)).hom'.map_smul a] at hd
  rw [map_smul]
  dsimp only [ConcreteCategory.hom]
  rw [hd]
  module

lemma oneKoszulCubeE02_d (a : R) :
    oneKoszulCubeE02 a ≫ (tensorCube (oneKoszulComplex a)).d (-2) (-1) =
      a • oneKoszulCubeE2 a - a • oneKoszulCubeE0 a := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change (tensorCube (oneKoszulComplex a)).d (-2) (-1)
    (r • (cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
      (-1) (0) (-1) (-2) (by omega)
      (((oneKoszulXNegOneIso a).inv 1 ⊗ₜ[R] (oneKoszulXZeroIso a).inv 1) ⊗ₜ[R]
        (oneKoszulXNegOneIso a).inv 1))) =
    a • (r • (cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
      (0) (0) (-1) (-1) (by omega)
      (((oneKoszulXZeroIso a).inv 1 ⊗ₜ[R] (oneKoszulXZeroIso a).inv 1) ⊗ₜ[R] (oneKoszulXNegOneIso
        a).inv 1))) -
    a • (r • (cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
      (-1) (0) (0) (-1) (by omega)
      (((oneKoszulXNegOneIso a).inv 1 ⊗ₜ[R] (oneKoszulXZeroIso a).inv 1) ⊗ₜ[R] (oneKoszulXZeroIso
        a).inv 1)))
  have hd := cochainTensorTriple_d_apply_ι
    (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
      (-1) (0) (-1) (-2) (by omega)
      ((oneKoszulXNegOneIso a).inv 1)
      ((oneKoszulXZeroIso a).inv 1)
      ((oneKoszulXNegOneIso a).inv 1)
  simp only [Int.reduceAdd, Int.reduceNeg] at hd
  rw [oneKoszulXNegOne_generator_d_apply a 1] at hd
  try rw [oneKoszulXZero_generator_d_apply a 1] at hd
  dsimp only [ConcreteCategory.hom] at hd
  simp only [TensorProduct.zero_tmul, TensorProduct.tmul_zero, moduleHom_map_zero, neg_zero,
    add_zero, Units.smul_def, Int.negOnePow_neg, Int.negOnePow_one, Units.val_neg, Units.val_one,
    neg_one_smul, ← TensorProduct.smul_tmul' (R := R) (R' := R), TensorProduct.tmul_smul (R := R)
    (R' := R)] at hd
  rw [(cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
    (0) (0) (-1) (-1) (by omega)).hom'.map_smul a] at hd
  rw [(cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
    (-1) (0) (0) (-1) (by omega)).hom'.map_smul a] at hd
  rw [map_smul]
  dsimp only [ConcreteCategory.hom]
  rw [hd]
  module

lemma oneKoszulCubeE12_d (a : R) :
    oneKoszulCubeE12 a ≫ (tensorCube (oneKoszulComplex a)).d (-2) (-1) =
      a • oneKoszulCubeE2 a - a • oneKoszulCubeE1 a := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change (tensorCube (oneKoszulComplex a)).d (-2) (-1)
    (r • (cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
      (0) (-1) (-1) (-2) (by omega)
      (((oneKoszulXZeroIso a).inv 1 ⊗ₜ[R] (oneKoszulXNegOneIso a).inv 1) ⊗ₜ[R]
        (oneKoszulXNegOneIso a).inv 1))) =
    a • (r • (cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
      (0) (0) (-1) (-1) (by omega)
      (((oneKoszulXZeroIso a).inv 1 ⊗ₜ[R] (oneKoszulXZeroIso a).inv 1) ⊗ₜ[R] (oneKoszulXNegOneIso
        a).inv 1))) -
    a • (r • (cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
      (0) (-1) (0) (-1) (by omega)
      (((oneKoszulXZeroIso a).inv 1 ⊗ₜ[R] (oneKoszulXNegOneIso a).inv 1) ⊗ₜ[R] (oneKoszulXZeroIso
        a).inv 1)))
  have hd := cochainTensorTriple_d_apply_ι
    (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
      (0) (-1) (-1) (-2) (by omega)
      ((oneKoszulXZeroIso a).inv 1)
      ((oneKoszulXNegOneIso a).inv 1)
      ((oneKoszulXNegOneIso a).inv 1)
  simp only [Int.reduceAdd, Int.reduceNeg] at hd
  rw [oneKoszulXNegOne_generator_d_apply a 1] at hd
  try rw [oneKoszulXZero_generator_d_apply a 1] at hd
  dsimp only [ConcreteCategory.hom] at hd
  simp only [TensorProduct.zero_tmul, moduleHom_map_zero, zero_add, Units.smul_def,
    Int.negOnePow_neg, Int.negOnePow_one, Int.negOnePow_zero, Units.val_neg, Units.val_one,
    one_smul, neg_one_smul, ←     TensorProduct.smul_tmul' (R := R) (R' := R),
    TensorProduct.tmul_smul (R := R) (R' := R)] at hd
  rw [(cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
    (0) (0) (-1) (-1) (by omega)).hom'.map_smul a] at hd
  rw [(cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
    (0) (-1) (0) (-1) (by omega)).hom'.map_smul a] at hd
  rw [map_smul]
  dsimp only [ConcreteCategory.hom]
  rw [hd]
  module

lemma oneKoszulCubeTop_d (a : R) :
    oneKoszulCubeTop a ≫ (tensorCube (oneKoszulComplex a)).d (-3) (-2) =
      a • oneKoszulCubeE12 a - a • oneKoszulCubeE02 a + a • oneKoszulCubeE01 a := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change (tensorCube (oneKoszulComplex a)).d (-3) (-2)
    (r • (cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
      (-1) (-1) (-1) (-3) (by omega)
      (((oneKoszulXNegOneIso a).inv 1 ⊗ₜ[R] (oneKoszulXNegOneIso a).inv 1) ⊗ₜ[R]
        (oneKoszulXNegOneIso a).inv 1))) =
    a • (r • (cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
      (0) (-1) (-1) (-2) (by omega)
      (((oneKoszulXZeroIso a).inv 1 ⊗ₜ[R] (oneKoszulXNegOneIso a).inv 1) ⊗ₜ[R]
        (oneKoszulXNegOneIso a).inv 1))) -
    a • (r • (cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
      (-1) (0) (-1) (-2) (by omega)
      (((oneKoszulXNegOneIso a).inv 1 ⊗ₜ[R] (oneKoszulXZeroIso a).inv 1) ⊗ₜ[R]
        (oneKoszulXNegOneIso a).inv 1))) +
    a • (r • (cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
      (-1) (-1) (0) (-2) (by omega)
      (((oneKoszulXNegOneIso a).inv 1 ⊗ₜ[R] (oneKoszulXNegOneIso a).inv 1) ⊗ₜ[R]
        (oneKoszulXZeroIso a).inv 1)))
  have hd := cochainTensorTriple_d_apply_ι
    (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
      (-1) (-1) (-1) (-3) (by omega)
      ((oneKoszulXNegOneIso a).inv 1)
      ((oneKoszulXNegOneIso a).inv 1)
      ((oneKoszulXNegOneIso a).inv 1)
  simp only [Int.reduceAdd, Int.reduceNeg] at hd
  rw [oneKoszulXNegOne_generator_d_apply a 1] at hd
  try rw [oneKoszulXZero_generator_d_apply a 1] at hd
  dsimp only [ConcreteCategory.hom] at hd
  simp only [Units.smul_def, Int.negOnePow_neg, Int.negOnePow_one, show (2 : ℤ).negOnePow = 1 from
    Int.negOnePow_two_mul 1, Units.val_neg, Units.val_one, one_smul, neg_one_smul, ←
    TensorProduct.smul_tmul' (R := R) (R'     := R), TensorProduct.tmul_smul (R := R) (R' := R)]
    at hd
  rw [(cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
    (0) (-1) (-1) (-2) (by omega)).hom'.map_smul a] at hd
  rw [(cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
    (-1) (0) (-1) (-2) (by omega)).hom'.map_smul a] at hd
  rw [(cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
    (-1) (-1) (0) (-2) (by omega)).hom'.map_smul a] at hd
  rw [map_smul]
  dsimp only [ConcreteCategory.hom]
  rw [hd]
  module

end Adams
end SerrePositivity

end KoszulCubeDifferentialPart

section KoszulCubeExtPart

set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
open scoped TensorProduct
variable {R : Type u} [CommRing R]
namespace Adams

lemma oneKoszulCubeSummand_hom_ext (a : R) (i j k n : ℤ) (h : i + j + k = n)
    (ei : (oneKoszulComplex a).X i ≅ ModuleCat.of R R)
    (ej : (oneKoszulComplex a).X j ≅ ModuleCat.of R R)
    (ek : (oneKoszulComplex a).X k ≅ ModuleCat.of R R)
    {Y : ModuleCat.{u} R} (f g : (tensorCube (oneKoszulComplex a)).X n ⟶ Y)
    (he : oneKoszulCubeGenerator a i j k n h ei.inv ej.inv ek.inv ≫ f =
      oneKoszulCubeGenerator a i j k n h ei.inv ej.inv ek.inv ≫ g) :
    cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
        i j k n h ≫ f =
      cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a) (oneKoszulComplex a)
        i j k n h ≫ g := by
  apply rankOneTensorTriple_hom_ext _ _ _ ei ej ek
  have hv := congrArg (fun α => α (1 : R)) he
  change f ((1 : R) • cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a)
      (oneKoszulComplex a) i j k n h ((ei.inv 1 ⊗ₜ[R] ej.inv 1) ⊗ₜ[R] ek.inv 1)) =
    g ((1 : R) • cochainTensorTripleι (oneKoszulComplex a) (oneKoszulComplex a)
      (oneKoszulComplex a) i j k n h ((ei.inv 1 ⊗ₜ[R] ej.inv 1) ⊗ₜ[R] ek.inv 1)) at hv
  simpa only [one_smul, comp_apply] using hv

lemma oneKoszulCubeXZero_hom_ext (a : R) {Y : ModuleCat.{u} R}
    {f g : (tensorCube (oneKoszulComplex a)).X (0) ⟶ Y}
    (h0 : oneKoszulCubeBottom a ≫ f = oneKoszulCubeBottom a ≫ g)
    : f = g := by
  let P := oneKoszulComplex a
  apply cochainTensorTriple_hom_ext P P P
  intro i j k h
  by_cases hi : i = -1 ∨ i = 0
  · by_cases hj : j = -1 ∨ j = 0
    · by_cases hk : k = -1 ∨ k = 0
      · rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rcases hk with rfl | rfl
        all_goals first
          | omega
          | apply oneKoszulCubeSummand_hom_ext a _ _ _ _ h
              (by first | exact oneKoszulXNegOneIso a | exact oneKoszulXZeroIso a)
              (by first | exact oneKoszulXNegOneIso a | exact oneKoszulXZeroIso a)
              (by first | exact oneKoszulXNegOneIso a | exact oneKoszulXZeroIso a)
            first | exact h0
      · have hz := oneKoszul_isZero_X_other a k (by tauto)
        exact ((tensorLeft (P.X i ⊗ P.X j : ModuleCat.{u} R)).map_isZero hz).eq_of_src _ _
    · have hz := oneKoszul_isZero_X_other a j (by tauto)
      exact ((tensorRight (P.X k)).map_isZero
        ((tensorLeft (P.X i)).map_isZero hz)).eq_of_src _ _
  · have hz := oneKoszul_isZero_X_other a i (by tauto)
    exact ((tensorRight (P.X k)).map_isZero
      ((tensorRight (P.X j)).map_isZero hz)).eq_of_src _ _

lemma oneKoszulCubeXNegOne_hom_ext (a : R) {Y : ModuleCat.{u} R}
    {f g : (tensorCube (oneKoszulComplex a)).X (-1) ⟶ Y}
    (h0 : oneKoszulCubeE0 a ≫ f = oneKoszulCubeE0 a ≫ g)
    (h1 : oneKoszulCubeE1 a ≫ f = oneKoszulCubeE1 a ≫ g)
    (h2 : oneKoszulCubeE2 a ≫ f = oneKoszulCubeE2 a ≫ g)
    : f = g := by
  let P := oneKoszulComplex a
  apply cochainTensorTriple_hom_ext P P P
  intro i j k h
  by_cases hi : i = -1 ∨ i = 0
  · by_cases hj : j = -1 ∨ j = 0
    · by_cases hk : k = -1 ∨ k = 0
      · rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rcases hk with rfl | rfl
        all_goals first
          | omega
          | apply oneKoszulCubeSummand_hom_ext a _ _ _ _ h
              (by first | exact oneKoszulXNegOneIso a | exact oneKoszulXZeroIso a)
              (by first | exact oneKoszulXNegOneIso a | exact oneKoszulXZeroIso a)
              (by first | exact oneKoszulXNegOneIso a | exact oneKoszulXZeroIso a)
            first | exact h0 | exact h1 | exact h2
      · have hz := oneKoszul_isZero_X_other a k (by tauto)
        exact ((tensorLeft (P.X i ⊗ P.X j : ModuleCat.{u} R)).map_isZero hz).eq_of_src _ _
    · have hz := oneKoszul_isZero_X_other a j (by tauto)
      exact ((tensorRight (P.X k)).map_isZero
        ((tensorLeft (P.X i)).map_isZero hz)).eq_of_src _ _
  · have hz := oneKoszul_isZero_X_other a i (by tauto)
    exact ((tensorRight (P.X k)).map_isZero
      ((tensorRight (P.X j)).map_isZero hz)).eq_of_src _ _

lemma oneKoszulCubeXNegTwo_hom_ext (a : R) {Y : ModuleCat.{u} R}
    {f g : (tensorCube (oneKoszulComplex a)).X (-2) ⟶ Y}
    (h0 : oneKoszulCubeE01 a ≫ f = oneKoszulCubeE01 a ≫ g)
    (h1 : oneKoszulCubeE02 a ≫ f = oneKoszulCubeE02 a ≫ g)
    (h2 : oneKoszulCubeE12 a ≫ f = oneKoszulCubeE12 a ≫ g)
    : f = g := by
  let P := oneKoszulComplex a
  apply cochainTensorTriple_hom_ext P P P
  intro i j k h
  by_cases hi : i = -1 ∨ i = 0
  · by_cases hj : j = -1 ∨ j = 0
    · by_cases hk : k = -1 ∨ k = 0
      · rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rcases hk with rfl | rfl
        all_goals first
          | omega
          | apply oneKoszulCubeSummand_hom_ext a _ _ _ _ h
              (by first | exact oneKoszulXNegOneIso a | exact oneKoszulXZeroIso a)
              (by first | exact oneKoszulXNegOneIso a | exact oneKoszulXZeroIso a)
              (by first | exact oneKoszulXNegOneIso a | exact oneKoszulXZeroIso a)
            first | exact h0 | exact h1 | exact h2
      · have hz := oneKoszul_isZero_X_other a k (by tauto)
        exact ((tensorLeft (P.X i ⊗ P.X j : ModuleCat.{u} R)).map_isZero hz).eq_of_src _ _
    · have hz := oneKoszul_isZero_X_other a j (by tauto)
      exact ((tensorRight (P.X k)).map_isZero
        ((tensorLeft (P.X i)).map_isZero hz)).eq_of_src _ _
  · have hz := oneKoszul_isZero_X_other a i (by tauto)
    exact ((tensorRight (P.X k)).map_isZero
      ((tensorRight (P.X j)).map_isZero hz)).eq_of_src _ _

lemma oneKoszulCubeXNegThree_hom_ext (a : R) {Y : ModuleCat.{u} R}
    {f g : (tensorCube (oneKoszulComplex a)).X (-3) ⟶ Y}
    (h0 : oneKoszulCubeTop a ≫ f = oneKoszulCubeTop a ≫ g)
    : f = g := by
  let P := oneKoszulComplex a
  apply cochainTensorTriple_hom_ext P P P
  intro i j k h
  by_cases hi : i = -1 ∨ i = 0
  · by_cases hj : j = -1 ∨ j = 0
    · by_cases hk : k = -1 ∨ k = 0
      · rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> rcases hk with rfl | rfl
        all_goals first
          | omega
          | apply oneKoszulCubeSummand_hom_ext a _ _ _ _ h
              (oneKoszulXNegOneIso a)
              (oneKoszulXNegOneIso a)
              (oneKoszulXNegOneIso a)
            first | exact h0
      · have hz := oneKoszul_isZero_X_other a k (by tauto)
        exact ((tensorLeft (P.X i ⊗ P.X j : ModuleCat.{u} R)).map_isZero hz).eq_of_src _ _
    · have hz := oneKoszul_isZero_X_other a j (by tauto)
      exact ((tensorRight (P.X k)).map_isZero
        ((tensorLeft (P.X i)).map_isZero hz)).eq_of_src _ _
  · have hz := oneKoszul_isZero_X_other a i (by tauto)
    exact ((tensorRight (P.X k)).map_isZero
      ((tensorRight (P.X j)).map_isZero hz)).eq_of_src _ _

end Adams
end SerrePositivity

end KoszulCubeExtPart

section KoszulCubeCoordinatesPart

set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
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

end KoszulCubeCoordinatesPart
