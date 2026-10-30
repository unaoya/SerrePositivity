module

public import SerrePositivity.KTheory.Adams.KoszulCubeGenerators
public import SerrePositivity.PerfectComplex.TensorHomotopy
public import SerrePositivity.HomologicalAlgebra.CochainTensorShuffle
public import SerrePositivity.HomologicalAlgebra.CochainTensorHomogeneous
public import SerrePositivity.HomologicalAlgebra.CochainTensorTriple
public import SerrePositivity.PerfectComplex.TensorSupport
public import SerrePositivity.HomologicalAlgebra.CochainTensorShift
public import SerrePositivity.HomologicalAlgebra.CochainTensorCone
public import SerrePositivity.HomologicalAlgebra.CochainTensorTripleDifferential

/-! # Differentials on the eight Koszul cube generators -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
universe u
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
