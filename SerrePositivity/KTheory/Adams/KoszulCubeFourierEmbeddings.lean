module

public import SerrePositivity.PerfectComplex.ClosedSupport.Functoriality
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic
public import SerrePositivity.HomologicalAlgebra.Complex.Basic
public import SerrePositivity.KTheory.Adams.KoszulCubeFourierBasis
public import SerrePositivity.KTheory.Adams.KoszulShiftOneModel
public import SerrePositivity.KTheory.Adams.KoszulShiftTwoModel

/-! # Four Fourier chain embeddings into the one-element Koszul cube -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex Preadditive
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace Adams

omit [Invertible (3 : R)] in
lemma oneKoszulCubeBottom_d (a : R) :
    oneKoszulCubeBottom a ≫ (tensorCube (oneKoszulComplex a)).d 0 1 = 0 := by
  have hd : (tensorCube (oneKoszulComplex a)).d 0 1 = 0 :=
    (oneKoszulCube_isZero_X_other a 1 (by omega)).eq_of_tgt _ _
  rw [hd, comp_zero]

def oneKoszulCubeFourierZeroEmbedding (a : R) :
    oneKoszulComplex a ⟶ tensorCube (oneKoszulComplex a) :=
  cochainTwoTermScalarMap _ _ (-1) 0 (oneKoszulXNegOneIso a) (oneKoszulXZeroIso a)
    (oneKoszulCubeFourierOneZero a) (oneKoszulCubeBottom a) (by omega)
    (oneKoszul_isZero_X_other a) a (oneKoszul_generator_d a)
    (oneKoszulCubeFourierOneZero_d a) (oneKoszulCubeBottom_d a)

lemma oneKoszulCubeFourierZeroEmbedding_rotation (a : R) :
    oneKoszulCubeFourierZeroEmbedding a ≫ tensorCubeRotation (oneKoszulComplex a) =
      oneKoszulCubeFourierZeroEmbedding a := by
  simpa only [oneKoszulCubeFourierZeroEmbedding, one_smul] using
    cochainTwoTermScalarMap_eigen _ _ (-1) 0 (oneKoszulXNegOneIso a) (oneKoszulXZeroIso a)
      (oneKoszulCubeFourierOneZero a) (oneKoszulCubeBottom a) (by omega)
      (oneKoszul_isZero_X_other a) a (oneKoszul_generator_d a)
      (oneKoszulCubeFourierOneZero_d a) (oneKoszulCubeBottom_d a)
      (tensorCubeRotation (oneKoszulComplex a)) (1 : R)
      (by simpa only [one_smul] using oneKoszulCubeFourierOneZero_rotation a)
      (by simpa only [one_smul] using oneKoszulCubeBottom_rotation a)

omit [Invertible (3 : R)] in
lemma oneKoszulShiftOne_generator_d_scalar (a : R) :
    (oneKoszulShiftOneXNegTwoIso a).inv ≫ (oneKoszulShiftOne a).d (-2) (-1) =
      (-a) • (oneKoszulShiftOneXNegOneIso a).inv := by
  rw [oneKoszulShiftOne_generator_d, neg_smul]

lemma oneKoszulCubeFourierTwo01_neg_d (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (-oneKoszulCubeFourierTwo01 a t) ≫ (tensorCube (oneKoszulComplex a)).d (-2) (-1) =
      (-a) • oneKoszulCubeFourierOneOne a t := by
  rw [neg_comp, oneKoszulCubeFourierTwo01_d a t ht, neg_smul]

def oneKoszulCubeFourierOneEmbedding (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulShiftOne a ⟶ tensorCube (oneKoszulComplex a) :=
  cochainTwoTermScalarMap _ _ (-2) (-1)
    (oneKoszulShiftOneXNegTwoIso a) (oneKoszulShiftOneXNegOneIso a)
    (-oneKoszulCubeFourierTwo01 a t) (oneKoszulCubeFourierOneOne a t) (by omega)
    (oneKoszulShiftOne_isZero_X_other a) (-a) (oneKoszulShiftOne_generator_d_scalar a)
    (oneKoszulCubeFourierTwo01_neg_d a t ht) (oneKoszulCubeFourierOneOne_d a t ht)

lemma oneKoszulCubeFourierOneEmbedding_rotation (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierOneEmbedding a t ht ≫ tensorCubeRotation (oneKoszulComplex a) =
      t • oneKoszulCubeFourierOneEmbedding a t ht := by
  exact cochainTwoTermScalarMap_eigen _ _ (-2) (-1)
    (oneKoszulShiftOneXNegTwoIso a) (oneKoszulShiftOneXNegOneIso a)
    (-oneKoszulCubeFourierTwo01 a t) (oneKoszulCubeFourierOneOne a t) (by omega)
    (oneKoszulShiftOne_isZero_X_other a) (-a) (oneKoszulShiftOne_generator_d_scalar a)
    (oneKoszulCubeFourierTwo01_neg_d a t ht) (oneKoszulCubeFourierOneOne_d a t ht)
    (tensorCubeRotation (oneKoszulComplex a)) (t)
    (by rw [neg_comp, oneKoszulCubeFourierTwo01_rotation a t ht, smul_neg])
    (oneKoszulCubeFourierOneOne_rotation a t ht)

lemma oneKoszulCubeFourierTwo02_neg_d (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (-oneKoszulCubeFourierTwo02 a t) ≫ (tensorCube (oneKoszulComplex a)).d (-2) (-1) =
      (-a) • oneKoszulCubeFourierOneTwo a t := by
  rw [neg_comp, oneKoszulCubeFourierTwo02_d a t ht, neg_smul]

def oneKoszulCubeFourierTwoEmbedding (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulShiftOne a ⟶ tensorCube (oneKoszulComplex a) :=
  cochainTwoTermScalarMap _ _ (-2) (-1)
    (oneKoszulShiftOneXNegTwoIso a) (oneKoszulShiftOneXNegOneIso a)
    (-oneKoszulCubeFourierTwo02 a t) (oneKoszulCubeFourierOneTwo a t) (by omega)
    (oneKoszulShiftOne_isZero_X_other a) (-a) (oneKoszulShiftOne_generator_d_scalar a)
    (oneKoszulCubeFourierTwo02_neg_d a t ht) (oneKoszulCubeFourierOneTwo_d a t ht)

lemma oneKoszulCubeFourierTwoEmbedding_rotation (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierTwoEmbedding a t ht ≫ tensorCubeRotation (oneKoszulComplex a) =
      t ^ 2 • oneKoszulCubeFourierTwoEmbedding a t ht := by
  exact cochainTwoTermScalarMap_eigen _ _ (-2) (-1)
    (oneKoszulShiftOneXNegTwoIso a) (oneKoszulShiftOneXNegOneIso a)
    (-oneKoszulCubeFourierTwo02 a t) (oneKoszulCubeFourierOneTwo a t) (by omega)
    (oneKoszulShiftOne_isZero_X_other a) (-a) (oneKoszulShiftOne_generator_d_scalar a)
    (oneKoszulCubeFourierTwo02_neg_d a t ht) (oneKoszulCubeFourierOneTwo_d a t ht)
    (tensorCubeRotation (oneKoszulComplex a)) (t ^ 2)
    (by rw [neg_comp, oneKoszulCubeFourierTwo02_rotation a t ht, smul_neg])
    (oneKoszulCubeFourierOneTwo_rotation a t ht)

def oneKoszulCubeFourierTopEmbedding (a t : R) :
    oneKoszulShiftTwo a ⟶ tensorCube (oneKoszulComplex a) :=
  cochainTwoTermScalarMap _ _ (-3) (-2)
    (oneKoszulShiftTwoXNegThreeIso a) (oneKoszulShiftTwoXNegTwoIso a)
    (oneKoszulCubeFourierTop a t) (oneKoszulCubeFourierTwo12 a t) (by omega)
    (oneKoszulShiftTwo_isZero_X_other a) a (oneKoszulShiftTwo_generator_d a)
    (oneKoszulCubeFourierTop_d a t) (oneKoszulCubeFourierTwo12_d a t)

lemma oneKoszulCubeFourierTopEmbedding_rotation (a t : R) :
    oneKoszulCubeFourierTopEmbedding a t ≫ tensorCubeRotation (oneKoszulComplex a) =
      oneKoszulCubeFourierTopEmbedding a t := by
  simpa only [oneKoszulCubeFourierTopEmbedding, one_smul] using
    cochainTwoTermScalarMap_eigen _ _ (-3) (-2)
      (oneKoszulShiftTwoXNegThreeIso a) (oneKoszulShiftTwoXNegTwoIso a)
      (oneKoszulCubeFourierTop a t) (oneKoszulCubeFourierTwo12 a t) (by omega)
      (oneKoszulShiftTwo_isZero_X_other a) a (oneKoszulShiftTwo_generator_d a)
      (oneKoszulCubeFourierTop_d a t) (oneKoszulCubeFourierTwo12_d a t)
      (tensorCubeRotation (oneKoszulComplex a)) (1 : R)
      (by simpa only [one_smul] using oneKoszulCubeFourierTop_rotation a t)
      (by simpa only [one_smul] using oneKoszulCubeFourierTwo12_rotation a t)

end Adams
end SerrePositivity
