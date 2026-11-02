module

public import SerrePositivity.KTheory.Adams.KoszulCube
public import SerrePositivity.PerfectComplex.CubicFourierEigen
public import SerrePositivity.PerfectComplex.CubicFourierMinorIdentities
public import SerrePositivity.HomologicalAlgebra.KoszulOneCoordinates
public import SerrePositivity.PerfectComplex.ClosedSupport.Functoriality
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic
public import SerrePositivity.HomologicalAlgebra.Complex.Basic
public import SerrePositivity.KTheory.Adams.KoszulSquareSplitting

/-! # Koszul のテンソル三乗の Fourier 座標

## 概要

次数 -1 の Fourier 固有ベクトルとその Koszul 微分、生成元の復元と双対座標、次数 -2 の Fourier 小行列式と次数 -3 の行列式、その逆の公式と双対座標、次数ごとの Fourier 基底の同型、一元 Koszul 三乗への四つの Fourier 鎖の埋め込み、二段シフトした一元 Koszul モデルを与える。

## 方針

1 の原始三乗根による離散 Fourier 変換を次数ごとに行い、逆変換を明示する。

## 規約

「環 R 上の位数 n の巡回群の離散 Fourier 変換」としての一般化は段階 3 の候補。

## 使われ方

`Adams/KoszulCubeFourierModel`。
-/

@[expose] public noncomputable section

universe u

section KoszulCubeFourierOnePart

set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex Preadditive
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace Adams

def oneKoszulCubeFourierOneZero (a : R) :=
  (⅟(3 : R)) • (oneKoszulCubeE0 a + oneKoszulCubeE1 a + oneKoszulCubeE2 a)

def oneKoszulCubeFourierOneOne (a t : R) :=
  (⅟(3 : R)) • (oneKoszulCubeE0 a + t ^ 2 • oneKoszulCubeE1 a + t • oneKoszulCubeE2 a)

def oneKoszulCubeFourierOneTwo (a t : R) :=
  (⅟(3 : R)) • (oneKoszulCubeE0 a + t • oneKoszulCubeE1 a + t ^ 2 • oneKoszulCubeE2 a)

lemma oneKoszulCubeFourierOneZero_rotation (a : R) :
    oneKoszulCubeFourierOneZero a ≫ (tensorCubeRotation (oneKoszulComplex a)).f (-1) =
      oneKoszulCubeFourierOneZero a := by
  simp only [oneKoszulCubeFourierOneZero, Linear.smul_comp, add_comp,
    oneKoszulCubeE0_rotation, oneKoszulCubeE1_rotation, oneKoszulCubeE2_rotation]
  module

lemma oneKoszulCubeFourierOneOne_rotation (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierOneOne a t ≫ (tensorCubeRotation (oneKoszulComplex a)).f (-1) =
      t • oneKoszulCubeFourierOneOne a t := by
  have hp : t * t ^ 2 = 1 := by
    rw [← pow_succ', cube_eq_one_of_cubic_relation t ht]
  simp only [oneKoszulCubeFourierOneOne, Linear.smul_comp, add_comp,
    oneKoszulCubeE0_rotation, oneKoszulCubeE1_rotation, oneKoszulCubeE2_rotation]
  rw [smul_comm t (⅟(3 : R))]
  congr 1
  simp only [smul_add, smul_smul, hp, one_smul, ← pow_two]
  module

lemma oneKoszulCubeFourierOneTwo_rotation (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierOneTwo a t ≫ (tensorCubeRotation (oneKoszulComplex a)).f (-1) =
      t ^ 2 • oneKoszulCubeFourierOneTwo a t := by
  have hc := cube_eq_one_of_cubic_relation t ht
  have hp : t ^ 2 * t = 1 := by rw [← pow_succ, hc]
  have hq : t ^ 2 * t ^ 2 = t := by
    calc
      _ = t ^ 3 * t := by ring
      _ = t := by rw [hc, one_mul]
  simp only [oneKoszulCubeFourierOneTwo, Linear.smul_comp, add_comp,
    oneKoszulCubeE0_rotation, oneKoszulCubeE1_rotation, oneKoszulCubeE2_rotation]
  rw [smul_comm (t ^ 2) (⅟(3 : R))]
  congr 1
  simp only [smul_add, smul_smul, hp, hq, one_smul]
  module

lemma oneKoszulCubeFourierOneZero_d (a : R) :
    oneKoszulCubeFourierOneZero a ≫ (tensorCube (oneKoszulComplex a)).d (-1) 0 =
      a • oneKoszulCubeBottom a := by
  simp only [oneKoszulCubeFourierOneZero, Linear.smul_comp, add_comp,
    oneKoszulCubeE0_d, oneKoszulCubeE1_d, oneKoszulCubeE2_d]
  calc
    _ = (⅟(3 : R)) • ((3 : R) • (a • oneKoszulCubeBottom a)) := by module
    _ = _ := by rw [smul_smul, invOf_mul_self, one_smul]

lemma oneKoszulCubeFourierOneOne_d (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierOneOne a t ≫ (tensorCube (oneKoszulComplex a)).d (-1) 0 = 0 := by
  simp only [oneKoszulCubeFourierOneOne, Linear.smul_comp, add_comp,
    oneKoszulCubeE0_d, oneKoszulCubeE1_d, oneKoszulCubeE2_d]
  calc
    _ = (⅟(3 : R)) • ((t ^ 2 + t + 1) • (a • oneKoszulCubeBottom a)) := by module
    _ = _ := by rw [ht, zero_smul, smul_zero]

lemma oneKoszulCubeFourierOneTwo_d (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierOneTwo a t ≫ (tensorCube (oneKoszulComplex a)).d (-1) 0 = 0 := by
  simp only [oneKoszulCubeFourierOneTwo, Linear.smul_comp, add_comp,
    oneKoszulCubeE0_d, oneKoszulCubeE1_d, oneKoszulCubeE2_d]
  calc
    _ = (⅟(3 : R)) • ((t ^ 2 + t + 1) • (a • oneKoszulCubeBottom a)) := by module
    _ = _ := by rw [ht, zero_smul, smul_zero]

end Adams
end SerrePositivity

end KoszulCubeFourierOnePart

section KoszulCubeFourierOneInversePart

set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace Adams

lemma oneKoszulCubeE0_fourier (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeE0 a = oneKoszulCubeFourierOneZero a +
      oneKoszulCubeFourierOneOne a t + oneKoszulCubeFourierOneTwo a t := by
  have hs : 1 + t + t ^ 2 = 0 := by linear_combination ht
  symm
  calc
    _ = (⅟(3 : R)) • ((3 : R) • oneKoszulCubeE0 a +
      (1 + t + t ^ 2) • oneKoszulCubeE1 a + (1 + t + t ^ 2) • oneKoszulCubeE2 a) := by
        unfold oneKoszulCubeFourierOneZero oneKoszulCubeFourierOneOne oneKoszulCubeFourierOneTwo
        module
    _ = _ := by
      rw [hs]
      simp only [zero_smul, add_zero, smul_smul, invOf_mul_self, one_smul]

lemma oneKoszulCubeE1_fourier (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeE1 a = oneKoszulCubeFourierOneZero a +
      t • oneKoszulCubeFourierOneOne a t + t ^ 2 • oneKoszulCubeFourierOneTwo a t := by
  have hc := cube_eq_one_of_cubic_relation t ht
  have hs : 1 + t + t ^ 2 = 0 := by linear_combination ht
  have hs' : 1 + t ^ 2 + t = 0 := by linear_combination ht
  have ht4 : t ^ 4 = t := by
    calc
      _ = t ^ 3 * t := by ring
      _ = t := by rw [hc, one_mul]
  symm
  calc
    _ = (⅟(3 : R)) • ((1 + t + t ^ 2) • oneKoszulCubeE0 a +
      (1 + t ^ 3 + t ^ 3) • oneKoszulCubeE1 a +
      (1 + t ^ 2 + t ^ 4) • oneKoszulCubeE2 a) := by
        unfold oneKoszulCubeFourierOneZero oneKoszulCubeFourierOneOne oneKoszulCubeFourierOneTwo
        module
    _ = _ := by
      rw [hc, ht4, hs, hs']
      simp only [zero_smul, zero_add, add_zero, show (1 + 1 + 1 : R) = 3 from by norm_num,
        smul_smul, invOf_mul_self, one_smul]

lemma oneKoszulCubeE2_fourier (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeE2 a = oneKoszulCubeFourierOneZero a +
      t ^ 2 • oneKoszulCubeFourierOneOne a t + t • oneKoszulCubeFourierOneTwo a t := by
  have hc := cube_eq_one_of_cubic_relation t ht
  have hs : 1 + t + t ^ 2 = 0 := by linear_combination ht
  have hs' : 1 + t ^ 2 + t = 0 := by linear_combination ht
  have ht4 : t ^ 4 = t := by
    calc
      _ = t ^ 3 * t := by ring
      _ = t := by rw [hc, one_mul]
  symm
  calc
    _ = (⅟(3 : R)) • ((1 + t + t ^ 2) • oneKoszulCubeE0 a +
      (1 + t ^ 2 + t ^ 4) • oneKoszulCubeE1 a +
      (1 + t ^ 3 + t ^ 3) • oneKoszulCubeE2 a) := by
        unfold oneKoszulCubeFourierOneZero oneKoszulCubeFourierOneOne oneKoszulCubeFourierOneTwo
        module
    _ = _ := by
      rw [hc, ht4, hs, hs']
      simp only [zero_smul, zero_add, add_zero, show (1 + 1 + 1 : R) = 3 from by norm_num,
        smul_smul, invOf_mul_self, one_smul]

end Adams
end SerrePositivity

end KoszulCubeFourierOneInversePart

section KoszulCubeFourierOneCoordinatesPart

set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex Preadditive
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace Adams

def oneKoszulCubeFourierOneZeroCoordinate (a : R) :=
  oneKoszulCubeE0Coordinate a + oneKoszulCubeE1Coordinate a + oneKoszulCubeE2Coordinate a

def oneKoszulCubeFourierOneOneCoordinate (a t : R) :=
  oneKoszulCubeE0Coordinate a + t • oneKoszulCubeE1Coordinate a + t ^ 2 •
    oneKoszulCubeE2Coordinate a

def oneKoszulCubeFourierOneTwoCoordinate (a t : R) :=
  oneKoszulCubeE0Coordinate a + t ^ 2 • oneKoszulCubeE1Coordinate a + t •
    oneKoszulCubeE2Coordinate a

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierOneZero_ZeroCoordinate (a : R) :
    oneKoszulCubeFourierOneZero a ≫ oneKoszulCubeFourierOneZeroCoordinate a = 𝟙 _ := by
  calc
    _ = (⅟(3 : R)) • ((3 : R) • (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶ ModuleCat.of R R)) := by
      unfold oneKoszulCubeFourierOneZero oneKoszulCubeFourierOneZeroCoordinate
      simp only [Linear.smul_comp, add_comp, comp_add,
        oneKoszulCubeE0_E0Coordinate,
        oneKoszulCubeE0_E1Coordinate,
        oneKoszulCubeE0_E2Coordinate,
        oneKoszulCubeE1_E0Coordinate,
        oneKoszulCubeE1_E1Coordinate,
        oneKoszulCubeE1_E2Coordinate,
        oneKoszulCubeE2_E0Coordinate,
        oneKoszulCubeE2_E1Coordinate,
        oneKoszulCubeE2_E2Coordinate]
      module
    _ = _ := by
      rw [smul_smul, invOf_mul_self, one_smul]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierOneZero_OneCoordinate (a t : R)
    (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierOneZero a ≫ oneKoszulCubeFourierOneOneCoordinate a t = 0 := by
  have hs : 1 + t + t ^ 2 = 0 := by linear_combination ht
  calc
    _ = (⅟(3 : R)) • ((1 + t + t ^ 2) • (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶ ModuleCat.of R
      R)) := by
      unfold oneKoszulCubeFourierOneZero oneKoszulCubeFourierOneOneCoordinate
      simp only [Linear.smul_comp, Linear.comp_smul, add_comp, comp_add,
        oneKoszulCubeE0_E0Coordinate,
        oneKoszulCubeE0_E1Coordinate,
        oneKoszulCubeE0_E2Coordinate,
        oneKoszulCubeE1_E0Coordinate,
        oneKoszulCubeE1_E1Coordinate,
        oneKoszulCubeE1_E2Coordinate,
        oneKoszulCubeE2_E0Coordinate,
        oneKoszulCubeE2_E1Coordinate,
        oneKoszulCubeE2_E2Coordinate]
      module
    _ = _ := by
      rw [hs]
      simp only [zero_smul, smul_zero]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierOneZero_TwoCoordinate (a t : R)
    (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierOneZero a ≫ oneKoszulCubeFourierOneTwoCoordinate a t = 0 := by
  have hs : 1 + t + t ^ 2 = 0 := by linear_combination ht
  calc
    _ = (⅟(3 : R)) • ((1 + t + t ^ 2) • (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶ ModuleCat.of R
      R)) := by
      unfold oneKoszulCubeFourierOneZero oneKoszulCubeFourierOneTwoCoordinate
      simp only [Linear.smul_comp, Linear.comp_smul, add_comp, comp_add,
        oneKoszulCubeE0_E0Coordinate,
        oneKoszulCubeE0_E1Coordinate,
        oneKoszulCubeE0_E2Coordinate,
        oneKoszulCubeE1_E0Coordinate,
        oneKoszulCubeE1_E1Coordinate,
        oneKoszulCubeE1_E2Coordinate,
        oneKoszulCubeE2_E0Coordinate,
        oneKoszulCubeE2_E1Coordinate,
        oneKoszulCubeE2_E2Coordinate]
      module
    _ = _ := by
      rw [hs]
      simp only [zero_smul, smul_zero]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierOneOne_ZeroCoordinate (a t : R)
    (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierOneOne a t ≫ oneKoszulCubeFourierOneZeroCoordinate a = 0 := by
  have hs : 1 + t + t ^ 2 = 0 := by linear_combination ht
  calc
    _ = (⅟(3 : R)) • ((1 + t + t ^ 2) • (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶ ModuleCat.of R
      R)) := by
      unfold oneKoszulCubeFourierOneOne oneKoszulCubeFourierOneZeroCoordinate
      simp only [Linear.smul_comp, add_comp, comp_add,
        oneKoszulCubeE0_E0Coordinate,
        oneKoszulCubeE0_E1Coordinate,
        oneKoszulCubeE0_E2Coordinate,
        oneKoszulCubeE1_E0Coordinate,
        oneKoszulCubeE1_E1Coordinate,
        oneKoszulCubeE1_E2Coordinate,
        oneKoszulCubeE2_E0Coordinate,
        oneKoszulCubeE2_E1Coordinate,
        oneKoszulCubeE2_E2Coordinate]
      module
    _ = _ := by
      rw [hs]
      simp only [zero_smul, smul_zero]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierOneOne_OneCoordinate (a t : R)
    (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierOneOne a t ≫ oneKoszulCubeFourierOneOneCoordinate a t = 𝟙 _ := by
  have hc := cube_eq_one_of_cubic_relation t ht
  have hs : 1 + t ^ 3 + t ^ 3 = (3 : R) := by rw [hc]; norm_num
  calc
    _ = (⅟(3 : R)) • ((1 + t ^ 3 + t ^ 3) • (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶
      ModuleCat.of R R)) := by
      unfold oneKoszulCubeFourierOneOne oneKoszulCubeFourierOneOneCoordinate
      simp only [Linear.smul_comp, Linear.comp_smul, add_comp, comp_add,
        oneKoszulCubeE0_E0Coordinate,
        oneKoszulCubeE0_E1Coordinate,
        oneKoszulCubeE0_E2Coordinate,
        oneKoszulCubeE1_E0Coordinate,
        oneKoszulCubeE1_E1Coordinate,
        oneKoszulCubeE1_E2Coordinate,
        oneKoszulCubeE2_E0Coordinate,
        oneKoszulCubeE2_E1Coordinate,
        oneKoszulCubeE2_E2Coordinate]
      module
    _ = _ := by
      rw [hs]
      rw [smul_smul, invOf_mul_self, one_smul]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierOneOne_TwoCoordinate (a t : R)
    (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierOneOne a t ≫ oneKoszulCubeFourierOneTwoCoordinate a t = 0 := by
  have hc := cube_eq_one_of_cubic_relation t ht
  have ht4 : t ^ 4 = t := by
    calc
      _ = t ^ 3 * t := by ring
      _ = t := by rw [hc, one_mul]
  have hs : 1 + t ^ 2 + t ^ 4 = 0 := by linear_combination ht + ht4
  calc
    _ = (⅟(3 : R)) • ((1 + t ^ 2 + t ^ 4) • (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶
      ModuleCat.of R R)) := by
      unfold oneKoszulCubeFourierOneOne oneKoszulCubeFourierOneTwoCoordinate
      simp only [Linear.smul_comp, Linear.comp_smul, add_comp, comp_add,
        oneKoszulCubeE0_E0Coordinate,
        oneKoszulCubeE0_E1Coordinate,
        oneKoszulCubeE0_E2Coordinate,
        oneKoszulCubeE1_E0Coordinate,
        oneKoszulCubeE1_E1Coordinate,
        oneKoszulCubeE1_E2Coordinate,
        oneKoszulCubeE2_E0Coordinate,
        oneKoszulCubeE2_E1Coordinate,
        oneKoszulCubeE2_E2Coordinate]
      module
    _ = _ := by
      rw [hs]
      simp only [zero_smul, smul_zero]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierOneTwo_ZeroCoordinate (a t : R)
    (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierOneTwo a t ≫ oneKoszulCubeFourierOneZeroCoordinate a = 0 := by
  have hs : 1 + t + t ^ 2 = 0 := by linear_combination ht
  calc
    _ = (⅟(3 : R)) • ((1 + t + t ^ 2) • (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶ ModuleCat.of R
      R)) := by
      unfold oneKoszulCubeFourierOneTwo oneKoszulCubeFourierOneZeroCoordinate
      simp only [Linear.smul_comp, add_comp, comp_add,
        oneKoszulCubeE0_E0Coordinate,
        oneKoszulCubeE0_E1Coordinate,
        oneKoszulCubeE0_E2Coordinate,
        oneKoszulCubeE1_E0Coordinate,
        oneKoszulCubeE1_E1Coordinate,
        oneKoszulCubeE1_E2Coordinate,
        oneKoszulCubeE2_E0Coordinate,
        oneKoszulCubeE2_E1Coordinate,
        oneKoszulCubeE2_E2Coordinate]
      module
    _ = _ := by
      rw [hs]
      simp only [zero_smul, smul_zero]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierOneTwo_OneCoordinate (a t : R)
    (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierOneTwo a t ≫ oneKoszulCubeFourierOneOneCoordinate a t = 0 := by
  have hc := cube_eq_one_of_cubic_relation t ht
  have ht4 : t ^ 4 = t := by
    calc
      _ = t ^ 3 * t := by ring
      _ = t := by rw [hc, one_mul]
  have hs : 1 + t ^ 2 + t ^ 4 = 0 := by linear_combination ht + ht4
  calc
    _ = (⅟(3 : R)) • ((1 + t ^ 2 + t ^ 4) • (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶
      ModuleCat.of R R)) := by
      unfold oneKoszulCubeFourierOneTwo oneKoszulCubeFourierOneOneCoordinate
      simp only [Linear.smul_comp, Linear.comp_smul, add_comp, comp_add,
        oneKoszulCubeE0_E0Coordinate,
        oneKoszulCubeE0_E1Coordinate,
        oneKoszulCubeE0_E2Coordinate,
        oneKoszulCubeE1_E0Coordinate,
        oneKoszulCubeE1_E1Coordinate,
        oneKoszulCubeE1_E2Coordinate,
        oneKoszulCubeE2_E0Coordinate,
        oneKoszulCubeE2_E1Coordinate,
        oneKoszulCubeE2_E2Coordinate]
      module
    _ = _ := by
      rw [hs]
      simp only [zero_smul, smul_zero]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierOneTwo_TwoCoordinate (a t : R)
    (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierOneTwo a t ≫ oneKoszulCubeFourierOneTwoCoordinate a t = 𝟙 _ := by
  have hc := cube_eq_one_of_cubic_relation t ht
  have hs : 1 + t ^ 3 + t ^ 3 = (3 : R) := by rw [hc]; norm_num
  calc
    _ = (⅟(3 : R)) • ((1 + t ^ 3 + t ^ 3) • (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶
      ModuleCat.of R R)) := by
      unfold oneKoszulCubeFourierOneTwo oneKoszulCubeFourierOneTwoCoordinate
      simp only [Linear.smul_comp, Linear.comp_smul, add_comp, comp_add,
        oneKoszulCubeE0_E0Coordinate,
        oneKoszulCubeE0_E1Coordinate,
        oneKoszulCubeE0_E2Coordinate,
        oneKoszulCubeE1_E0Coordinate,
        oneKoszulCubeE1_E1Coordinate,
        oneKoszulCubeE1_E2Coordinate,
        oneKoszulCubeE2_E0Coordinate,
        oneKoszulCubeE2_E1Coordinate,
        oneKoszulCubeE2_E2Coordinate]
      module
    _ = _ := by
      rw [hs]
      rw [smul_smul, invOf_mul_self, one_smul]

end Adams
end SerrePositivity

end KoszulCubeFourierOneCoordinatesPart

section KoszulCubeFourierTwoPart

set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex Preadditive
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace Adams

/-- The minor column corresponding to v₀ wedge v₁. -/
def oneKoszulCubeFourierTwo01 (a t : R) :=
  (⅟(3 : R)) ^ 2 • ((t ^ 2 - 1) • oneKoszulCubeE01 a +
    (t - 1) • oneKoszulCubeE02 a + (t - t ^ 2) • oneKoszulCubeE12 a)

/-- The minor column corresponding to v₀ wedge v₂. -/
def oneKoszulCubeFourierTwo02 (a t : R) :=
  (⅟(3 : R)) ^ 2 • ((t - 1) • oneKoszulCubeE01 a +
    (t ^ 2 - 1) • oneKoszulCubeE02 a + (t ^ 2 - t) • oneKoszulCubeE12 a)

/-- The minor column corresponding to v₁ wedge v₂. -/
def oneKoszulCubeFourierTwo12 (a t : R) :=
  ((⅟(3 : R)) ^ 2 * (t - t ^ 2)) •
    (oneKoszulCubeE01 a - oneKoszulCubeE02 a + oneKoszulCubeE12 a)

/-- The determinant column corresponding to v₀ wedge v₁ wedge v₂. -/
def oneKoszulCubeFourierTop (a t : R) :=
  ((⅟(3 : R)) ^ 2 * (t - t ^ 2)) • oneKoszulCubeTop a

lemma oneKoszulCubeFourierTwo01_rotation (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierTwo01 a t ≫ (tensorCubeRotation (oneKoszulComplex a)).f (-2) =
      t • oneKoszulCubeFourierTwo01 a t := by
  have hc := cube_eq_one_of_cubic_relation t ht
  have h0 : t * (t ^ 2 - 1) = 1 - t := by linear_combination hc
  have h1 : t * (t - 1) = t ^ 2 - t := by ring
  have h2 : t * (t - t ^ 2) = t ^ 2 - 1 := by linear_combination -hc
  simp only [oneKoszulCubeFourierTwo01, Linear.smul_comp, add_comp,
    oneKoszulCubeE01_rotation, oneKoszulCubeE02_rotation, oneKoszulCubeE12_rotation]
  rw [smul_comm t ((⅟(3 : R)) ^ 2)]
  congr 1
  simp only [smul_add, smul_smul, h0, h1, h2]
  module

lemma oneKoszulCubeFourierTwo02_rotation (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierTwo02 a t ≫ (tensorCubeRotation (oneKoszulComplex a)).f (-2) =
      t ^ 2 • oneKoszulCubeFourierTwo02 a t := by
  have hc := cube_eq_one_of_cubic_relation t ht
  have ht4 : t ^ 4 = t := by
    calc
      _ = t ^ 3 * t := by ring
      _ = t := by rw [hc, one_mul]
  have h0 : t ^ 2 * (t - 1) = 1 - t ^ 2 := by linear_combination hc
  have h1 : t ^ 2 * (t ^ 2 - 1) = t - t ^ 2 := by linear_combination ht4
  have h2 : t ^ 2 * (t ^ 2 - t) = t - 1 := by linear_combination ht4 - hc
  simp only [oneKoszulCubeFourierTwo02, Linear.smul_comp, add_comp,
    oneKoszulCubeE01_rotation, oneKoszulCubeE02_rotation, oneKoszulCubeE12_rotation]
  rw [smul_comm (t ^ 2) ((⅟(3 : R)) ^ 2)]
  congr 1
  simp only [smul_add, smul_smul, h0, h1, h2]
  module

lemma oneKoszulCubeFourierTwo12_rotation (a t : R) :
    oneKoszulCubeFourierTwo12 a t ≫ (tensorCubeRotation (oneKoszulComplex a)).f (-2) =
      oneKoszulCubeFourierTwo12 a t := by
  simp only [oneKoszulCubeFourierTwo12, Linear.smul_comp, add_comp, sub_comp,
    oneKoszulCubeE01_rotation, oneKoszulCubeE02_rotation, oneKoszulCubeE12_rotation]
  module

lemma oneKoszulCubeFourierTop_rotation (a t : R) :
    oneKoszulCubeFourierTop a t ≫ (tensorCubeRotation (oneKoszulComplex a)).f (-3) =
      oneKoszulCubeFourierTop a t := by
  simp only [oneKoszulCubeFourierTop, Linear.smul_comp, oneKoszulCubeTop_rotation]

lemma oneKoszulCubeFourierTwo01_d (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierTwo01 a t ≫ (tensorCube (oneKoszulComplex a)).d (-2) (-1) =
      a • oneKoszulCubeFourierOneOne a t := by
  have h0 : 2 - t - t ^ 2 = 3 := by linear_combination -ht
  have h1 : 2 * t ^ 2 - t - 1 = 3 * t ^ 2 := by linear_combination -ht
  have h2 : 2 * t - t ^ 2 - 1 = 3 * t := by linear_combination -ht
  have hi : (⅟(3 : R)) ^ 2 * 3 = ⅟(3 : R) := by
    rw [pow_two, mul_assoc, invOf_mul_self, mul_one]
  simp only [oneKoszulCubeFourierTwo01, Linear.smul_comp, add_comp,
    oneKoszulCubeE01_d, oneKoszulCubeE02_d, oneKoszulCubeE12_d]
  calc
    _ = (⅟(3 : R)) ^ 2 • ((2 - t - t ^ 2) • (a • oneKoszulCubeE0 a) +
      (2 * t ^ 2 - t - 1) • (a • oneKoszulCubeE1 a) +
      (2 * t - t ^ 2 - 1) • (a • oneKoszulCubeE2 a)) := by module
    _ = (⅟(3 : R)) ^ 2 • ((3 : R) •
      (a • (oneKoszulCubeE0 a + t ^ 2 • oneKoszulCubeE1 a + t • oneKoszulCubeE2 a))) := by
        rw [h0, h1, h2]
        module
    _ = _ := by
      rw [smul_smul, hi]
      unfold oneKoszulCubeFourierOneOne
      module

lemma oneKoszulCubeFourierTwo02_d (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierTwo02 a t ≫ (tensorCube (oneKoszulComplex a)).d (-2) (-1) =
      a • oneKoszulCubeFourierOneTwo a t := by
  have h0 : 2 - t - t ^ 2 = 3 := by linear_combination -ht
  have h1 : 2 * t - t ^ 2 - 1 = 3 * t := by linear_combination -ht
  have h2 : 2 * t ^ 2 - t - 1 = 3 * t ^ 2 := by linear_combination -ht
  have hi : (⅟(3 : R)) ^ 2 * 3 = ⅟(3 : R) := by
    rw [pow_two, mul_assoc, invOf_mul_self, mul_one]
  simp only [oneKoszulCubeFourierTwo02, Linear.smul_comp, add_comp,
    oneKoszulCubeE01_d, oneKoszulCubeE02_d, oneKoszulCubeE12_d]
  calc
    _ = (⅟(3 : R)) ^ 2 • ((2 - t - t ^ 2) • (a • oneKoszulCubeE0 a) +
      (2 * t - t ^ 2 - 1) • (a • oneKoszulCubeE1 a) +
      (2 * t ^ 2 - t - 1) • (a • oneKoszulCubeE2 a)) := by module
    _ = (⅟(3 : R)) ^ 2 • ((3 : R) •
      (a • (oneKoszulCubeE0 a + t • oneKoszulCubeE1 a + t ^ 2 • oneKoszulCubeE2 a))) := by
        rw [h0, h1, h2]
        module
    _ = _ := by
      rw [smul_smul, hi]
      unfold oneKoszulCubeFourierOneTwo
      module

lemma oneKoszulCubeFourierTwo12_d (a t : R) :
    oneKoszulCubeFourierTwo12 a t ≫ (tensorCube (oneKoszulComplex a)).d (-2) (-1) = 0 := by
  simp only [oneKoszulCubeFourierTwo12, Linear.smul_comp, add_comp, sub_comp,
    oneKoszulCubeE01_d, oneKoszulCubeE02_d, oneKoszulCubeE12_d]
  module

lemma oneKoszulCubeFourierTop_d (a t : R) :
    oneKoszulCubeFourierTop a t ≫ (tensorCube (oneKoszulComplex a)).d (-3) (-2) =
      a • oneKoszulCubeFourierTwo12 a t := by
  simp only [oneKoszulCubeFourierTop, oneKoszulCubeFourierTwo12, Linear.smul_comp,
    oneKoszulCubeTop_d]
  module

end Adams
end SerrePositivity

end KoszulCubeFourierTwoPart

section KoszulCubeFourierTwoInversePart

set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace Adams

lemma oneKoszulCubeE01_fourier (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeE01 a = (t - 1) • oneKoszulCubeFourierTwo01 a t +
      (t ^ 2 - 1) • oneKoszulCubeFourierTwo02 a t -
      (t - t ^ 2) • oneKoszulCubeFourierTwo12 a t := by
  have hd : 2 * (t ^ 2 - 1) * (t - 1) - (t - t ^ 2) ^ 2 = 9 := by
    linear_combination 2 * cubicFourierMinor_pair_product t ht -
      cubicFourierMinor_difference_square t ht
  have hz : (t ^ 2 - 1) ^ 2 + (t - 1) ^ 2 + (t - t ^ 2) ^ 2 = 0 := by
    linear_combination cubicFourierMinor_pair_square_sum t ht +
      cubicFourierMinor_difference_square t ht
  symm
  calc
    _ = (⅟(3 : R)) ^ 2 •
      ((2 * (t ^ 2 - 1) * (t - 1) - (t - t ^ 2) ^ 2) • oneKoszulCubeE01 a +
      ((t ^ 2 - 1) ^ 2 + (t - 1) ^ 2 + (t - t ^ 2) ^ 2) • oneKoszulCubeE02 a) := by
        unfold oneKoszulCubeFourierTwo01 oneKoszulCubeFourierTwo02 oneKoszulCubeFourierTwo12
        module
    _ = _ := by
      rw [hd, hz]
      simp only [zero_smul, add_zero, smul_smul, cubicFourierMinor_inverse_three_squared, one_smul]

lemma oneKoszulCubeE02_fourier (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeE02 a = (t ^ 2 - 1) • oneKoszulCubeFourierTwo01 a t +
      (t - 1) • oneKoszulCubeFourierTwo02 a t +
      (t - t ^ 2) • oneKoszulCubeFourierTwo12 a t := by
  have hd : 2 * (t ^ 2 - 1) * (t - 1) - (t - t ^ 2) ^ 2 = 9 := by
    linear_combination 2 * cubicFourierMinor_pair_product t ht -
      cubicFourierMinor_difference_square t ht
  have hz : (t ^ 2 - 1) ^ 2 + (t - 1) ^ 2 + (t - t ^ 2) ^ 2 = 0 := by
    linear_combination cubicFourierMinor_pair_square_sum t ht +
      cubicFourierMinor_difference_square t ht
  symm
  calc
    _ = (⅟(3 : R)) ^ 2 •
      (((t ^ 2 - 1) ^ 2 + (t - 1) ^ 2 + (t - t ^ 2) ^ 2) • oneKoszulCubeE01 a +
      (2 * (t ^ 2 - 1) * (t - 1) - (t - t ^ 2) ^ 2) • oneKoszulCubeE02 a) := by
        unfold oneKoszulCubeFourierTwo01 oneKoszulCubeFourierTwo02 oneKoszulCubeFourierTwo12
        module
    _ = _ := by
      rw [hd, hz]
      simp only [zero_smul, zero_add, smul_smul, cubicFourierMinor_inverse_three_squared, one_smul]

lemma oneKoszulCubeE12_fourier (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeE12 a = -(t - t ^ 2) •
      (oneKoszulCubeFourierTwo01 a t - oneKoszulCubeFourierTwo02 a t +
        oneKoszulCubeFourierTwo12 a t) := by
  have hd : -3 * (t - t ^ 2) ^ 2 = 9 := by
    linear_combination -3 * cubicFourierMinor_difference_square t ht
  symm
  calc
    _ = (⅟(3 : R)) ^ 2 • ((-3 * (t - t ^ 2) ^ 2) • oneKoszulCubeE12 a) := by
      unfold oneKoszulCubeFourierTwo01 oneKoszulCubeFourierTwo02 oneKoszulCubeFourierTwo12
      module
    _ = _ := by
      rw [hd, smul_smul, cubicFourierMinor_inverse_three_squared, one_smul]

lemma oneKoszulCubeTop_fourier (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeTop a = (3 * (t ^ 2 - t)) • oneKoszulCubeFourierTop a t := by
  have hd : -3 * (t - t ^ 2) ^ 2 = 9 := by
    linear_combination -3 * cubicFourierMinor_difference_square t ht
  symm
  calc
    _ = (⅟(3 : R)) ^ 2 • ((-3 * (t - t ^ 2) ^ 2) • oneKoszulCubeTop a) := by
      unfold oneKoszulCubeFourierTop
      module
    _ = _ := by
      rw [hd, smul_smul, cubicFourierMinor_inverse_three_squared, one_smul]

end Adams
end SerrePositivity

end KoszulCubeFourierTwoInversePart

section KoszulCubeFourierTwoCoordinatesPart

set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex Preadditive
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace Adams

def oneKoszulCubeFourierTwo01Coordinate (a t : R) :=
  (t - 1) • oneKoszulCubeE01Coordinate a + (t ^ 2 - 1) • oneKoszulCubeE02Coordinate a -
    (t - t ^ 2) • oneKoszulCubeE12Coordinate a

def oneKoszulCubeFourierTwo02Coordinate (a t : R) :=
  (t ^ 2 - 1) • oneKoszulCubeE01Coordinate a + (t - 1) • oneKoszulCubeE02Coordinate a +
    (t - t ^ 2) • oneKoszulCubeE12Coordinate a

def oneKoszulCubeFourierTwo12Coordinate (a t : R) :=
  -(t - t ^ 2) • (oneKoszulCubeE01Coordinate a - oneKoszulCubeE02Coordinate a +
    oneKoszulCubeE12Coordinate a)

def oneKoszulCubeFourierTopCoordinate (a t : R) :=
  (3 * (t ^ 2 - t)) • oneKoszulCubeTopCoordinate a

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierTwo01_Two01Coordinate (a t : R)
    (ht : t ^ 2 + t + 1 = 0)
    : oneKoszulCubeFourierTwo01 a t ≫ oneKoszulCubeFourierTwo01Coordinate a t = 𝟙 _ := by
  have hs : 2 * (t ^ 2 - 1) * (t - 1) - (t - t ^ 2) ^ 2 = 9 := by
    linear_combination 2 * cubicFourierMinor_pair_product t ht -
      cubicFourierMinor_difference_square t ht
  calc
    _ = (⅟(3 : R)) ^ 2 • ((2 * (t ^ 2 - 1) * (t - 1) - (t - t ^ 2) ^ 2 : R) •
      (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶ ModuleCat.of R R)) := by
        unfold oneKoszulCubeFourierTwo01 oneKoszulCubeFourierTwo01Coordinate
        simp only [Linear.smul_comp, Linear.comp_smul, add_comp, comp_add, comp_sub,
          oneKoszulCubeE01_E01Coordinate,
        oneKoszulCubeE01_E02Coordinate,
        oneKoszulCubeE01_E12Coordinate,
        oneKoszulCubeE02_E01Coordinate,
        oneKoszulCubeE02_E02Coordinate,
        oneKoszulCubeE02_E12Coordinate,
        oneKoszulCubeE12_E01Coordinate,
        oneKoszulCubeE12_E02Coordinate,
        oneKoszulCubeE12_E12Coordinate]
        module
    _ = _ := by
      rw [hs]
      rw [smul_smul, cubicFourierMinor_inverse_three_squared, one_smul]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierTwo01_Two02Coordinate (a t : R)
    (ht : t ^ 2 + t + 1 = 0)
    : oneKoszulCubeFourierTwo01 a t ≫ oneKoszulCubeFourierTwo02Coordinate a t = 0 := by
  have hs : (t ^ 2 - 1) ^ 2 + (t - 1) ^ 2 + (t - t ^ 2) ^ 2 = 0 := by
    linear_combination cubicFourierMinor_pair_square_sum t ht +
      cubicFourierMinor_difference_square t ht
  calc
    _ = (⅟(3 : R)) ^ 2 • (((t ^ 2 - 1) ^ 2 + (t - 1) ^ 2 + (t - t ^ 2) ^ 2 : R) •
      (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶ ModuleCat.of R R)) := by
        unfold oneKoszulCubeFourierTwo01 oneKoszulCubeFourierTwo02Coordinate
        simp only [Linear.smul_comp, Linear.comp_smul, add_comp, comp_add,
          oneKoszulCubeE01_E01Coordinate,
        oneKoszulCubeE01_E02Coordinate,
        oneKoszulCubeE01_E12Coordinate,
        oneKoszulCubeE02_E01Coordinate,
        oneKoszulCubeE02_E02Coordinate,
        oneKoszulCubeE02_E12Coordinate,
        oneKoszulCubeE12_E01Coordinate,
        oneKoszulCubeE12_E02Coordinate,
        oneKoszulCubeE12_E12Coordinate]
        module
    _ = _ := by
      rw [hs]
      simp only [zero_smul, smul_zero]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierTwo01_Two12Coordinate (a t : R)
    : oneKoszulCubeFourierTwo01 a t ≫ oneKoszulCubeFourierTwo12Coordinate a t = 0 := by
  calc
    _ = (⅟(3 : R)) ^ 2 • ((0 : R) •
      (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶ ModuleCat.of R R)) := by
        unfold oneKoszulCubeFourierTwo01 oneKoszulCubeFourierTwo12Coordinate
        simp only [Linear.smul_comp, Linear.comp_smul, add_comp, comp_add, comp_sub,
          oneKoszulCubeE01_E01Coordinate,
        oneKoszulCubeE01_E02Coordinate,
        oneKoszulCubeE01_E12Coordinate,
        oneKoszulCubeE02_E01Coordinate,
        oneKoszulCubeE02_E02Coordinate,
        oneKoszulCubeE02_E12Coordinate,
        oneKoszulCubeE12_E01Coordinate,
        oneKoszulCubeE12_E02Coordinate,
        oneKoszulCubeE12_E12Coordinate]
        module
    _ = _ := by
      simp only [zero_smul, smul_zero]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierTwo02_Two01Coordinate (a t : R)
    (ht : t ^ 2 + t + 1 = 0)
    : oneKoszulCubeFourierTwo02 a t ≫ oneKoszulCubeFourierTwo01Coordinate a t = 0 := by
  have hs : (t ^ 2 - 1) ^ 2 + (t - 1) ^ 2 + (t - t ^ 2) ^ 2 = 0 := by
    linear_combination cubicFourierMinor_pair_square_sum t ht +
      cubicFourierMinor_difference_square t ht
  calc
    _ = (⅟(3 : R)) ^ 2 • (((t ^ 2 - 1) ^ 2 + (t - 1) ^ 2 + (t - t ^ 2) ^ 2 : R) •
      (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶ ModuleCat.of R R)) := by
        unfold oneKoszulCubeFourierTwo02 oneKoszulCubeFourierTwo01Coordinate
        simp only [Linear.smul_comp, Linear.comp_smul, add_comp, comp_add, comp_sub,
          oneKoszulCubeE01_E01Coordinate,
        oneKoszulCubeE01_E02Coordinate,
        oneKoszulCubeE01_E12Coordinate,
        oneKoszulCubeE02_E01Coordinate,
        oneKoszulCubeE02_E02Coordinate,
        oneKoszulCubeE02_E12Coordinate,
        oneKoszulCubeE12_E01Coordinate,
        oneKoszulCubeE12_E02Coordinate,
        oneKoszulCubeE12_E12Coordinate]
        module
    _ = _ := by
      rw [hs]
      simp only [zero_smul, smul_zero]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierTwo02_Two02Coordinate (a t : R)
    (ht : t ^ 2 + t + 1 = 0)
    : oneKoszulCubeFourierTwo02 a t ≫ oneKoszulCubeFourierTwo02Coordinate a t = 𝟙 _ := by
  have hs : 2 * (t ^ 2 - 1) * (t - 1) - (t - t ^ 2) ^ 2 = 9 := by
    linear_combination 2 * cubicFourierMinor_pair_product t ht -
      cubicFourierMinor_difference_square t ht
  calc
    _ = (⅟(3 : R)) ^ 2 • ((2 * (t ^ 2 - 1) * (t - 1) - (t - t ^ 2) ^ 2 : R) •
      (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶ ModuleCat.of R R)) := by
        unfold oneKoszulCubeFourierTwo02 oneKoszulCubeFourierTwo02Coordinate
        simp only [Linear.smul_comp, Linear.comp_smul, add_comp, comp_add,
          oneKoszulCubeE01_E01Coordinate,
        oneKoszulCubeE01_E02Coordinate,
        oneKoszulCubeE01_E12Coordinate,
        oneKoszulCubeE02_E01Coordinate,
        oneKoszulCubeE02_E02Coordinate,
        oneKoszulCubeE02_E12Coordinate,
        oneKoszulCubeE12_E01Coordinate,
        oneKoszulCubeE12_E02Coordinate,
        oneKoszulCubeE12_E12Coordinate]
        module
    _ = _ := by
      rw [hs]
      rw [smul_smul, cubicFourierMinor_inverse_three_squared, one_smul]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierTwo02_Two12Coordinate (a t : R)
    : oneKoszulCubeFourierTwo02 a t ≫ oneKoszulCubeFourierTwo12Coordinate a t = 0 := by
  calc
    _ = (⅟(3 : R)) ^ 2 • ((0 : R) •
      (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶ ModuleCat.of R R)) := by
        unfold oneKoszulCubeFourierTwo02 oneKoszulCubeFourierTwo12Coordinate
        simp only [Linear.smul_comp, Linear.comp_smul, add_comp, comp_add, comp_sub,
          oneKoszulCubeE01_E01Coordinate,
        oneKoszulCubeE01_E02Coordinate,
        oneKoszulCubeE01_E12Coordinate,
        oneKoszulCubeE02_E01Coordinate,
        oneKoszulCubeE02_E02Coordinate,
        oneKoszulCubeE02_E12Coordinate,
        oneKoszulCubeE12_E01Coordinate,
        oneKoszulCubeE12_E02Coordinate,
        oneKoszulCubeE12_E12Coordinate]
        module
    _ = _ := by
      simp only [zero_smul, smul_zero]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierTwo12_Two01Coordinate (a t : R)
    : oneKoszulCubeFourierTwo12 a t ≫ oneKoszulCubeFourierTwo01Coordinate a t = 0 := by
  calc
    _ = (⅟(3 : R)) ^ 2 • ((0 : R) •
      (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶ ModuleCat.of R R)) := by
        unfold oneKoszulCubeFourierTwo12 oneKoszulCubeFourierTwo01Coordinate
        simp only [Linear.smul_comp, Linear.comp_smul, add_comp, sub_comp, comp_add, comp_sub,
          oneKoszulCubeE01_E01Coordinate,
        oneKoszulCubeE01_E02Coordinate,
        oneKoszulCubeE01_E12Coordinate,
        oneKoszulCubeE02_E01Coordinate,
        oneKoszulCubeE02_E02Coordinate,
        oneKoszulCubeE02_E12Coordinate,
        oneKoszulCubeE12_E01Coordinate,
        oneKoszulCubeE12_E02Coordinate,
        oneKoszulCubeE12_E12Coordinate]
        module
    _ = _ := by
      simp only [zero_smul, smul_zero]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierTwo12_Two02Coordinate (a t : R)
    : oneKoszulCubeFourierTwo12 a t ≫ oneKoszulCubeFourierTwo02Coordinate a t = 0 := by
  calc
    _ = (⅟(3 : R)) ^ 2 • ((0 : R) •
      (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶ ModuleCat.of R R)) := by
        unfold oneKoszulCubeFourierTwo12 oneKoszulCubeFourierTwo02Coordinate
        simp only [Linear.smul_comp, Linear.comp_smul, add_comp, sub_comp, comp_add,
          oneKoszulCubeE01_E01Coordinate,
        oneKoszulCubeE01_E02Coordinate,
        oneKoszulCubeE01_E12Coordinate,
        oneKoszulCubeE02_E01Coordinate,
        oneKoszulCubeE02_E02Coordinate,
        oneKoszulCubeE02_E12Coordinate,
        oneKoszulCubeE12_E01Coordinate,
        oneKoszulCubeE12_E02Coordinate,
        oneKoszulCubeE12_E12Coordinate]
        module
    _ = _ := by
      simp only [zero_smul, smul_zero]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierTwo12_Two12Coordinate (a t : R)
    (ht : t ^ 2 + t + 1 = 0)
    : oneKoszulCubeFourierTwo12 a t ≫ oneKoszulCubeFourierTwo12Coordinate a t = 𝟙 _ := by
  have hs : -3 * (t - t ^ 2) ^ 2 = 9 := by
    linear_combination -3 * cubicFourierMinor_difference_square t ht
  calc
    _ = (⅟(3 : R)) ^ 2 • ((-3 * (t - t ^ 2) ^ 2 : R) •
      (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶ ModuleCat.of R R)) := by
        unfold oneKoszulCubeFourierTwo12 oneKoszulCubeFourierTwo12Coordinate
        simp only [Linear.smul_comp, Linear.comp_smul, add_comp, sub_comp, comp_add, comp_sub,
          oneKoszulCubeE01_E01Coordinate,
        oneKoszulCubeE01_E02Coordinate,
        oneKoszulCubeE01_E12Coordinate,
        oneKoszulCubeE02_E01Coordinate,
        oneKoszulCubeE02_E02Coordinate,
        oneKoszulCubeE02_E12Coordinate,
        oneKoszulCubeE12_E01Coordinate,
        oneKoszulCubeE12_E02Coordinate,
        oneKoszulCubeE12_E12Coordinate]
        module
    _ = _ := by
      rw [hs]
      rw [smul_smul, cubicFourierMinor_inverse_three_squared, one_smul]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierTop_TopCoordinate (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierTop a t ≫ oneKoszulCubeFourierTopCoordinate a t = 𝟙 _ := by
  have hs : -3 * (t - t ^ 2) ^ 2 = 9 := by
    linear_combination -3 * cubicFourierMinor_difference_square t ht
  calc
    _ = (⅟(3 : R)) ^ 2 • ((-3 * (t - t ^ 2) ^ 2) •
      (𝟙 (ModuleCat.of R R) : ModuleCat.of R R ⟶ ModuleCat.of R R)) := by
        unfold oneKoszulCubeFourierTop oneKoszulCubeFourierTopCoordinate
        simp only [Linear.smul_comp, Linear.comp_smul, oneKoszulCubeTop_TopCoordinate]
        module
    _ = _ := by rw [hs, smul_smul, cubicFourierMinor_inverse_three_squared, one_smul]

end Adams
end SerrePositivity

end KoszulCubeFourierTwoCoordinatesPart

section KoszulCubeFourierBasisPart

set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex Preadditive
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace Adams

lemma oneKoszulCubeFourierOne_hom_ext (a t : R) (ht : t ^ 2 + t + 1 = 0)
    {Y : ModuleCat.{u} R} {f g : (tensorCube (oneKoszulComplex a)).X (-1) ⟶ Y}
    (h0 : oneKoszulCubeFourierOneZero a ≫ f = oneKoszulCubeFourierOneZero a ≫ g)
    (h1 : oneKoszulCubeFourierOneOne a t ≫ f = oneKoszulCubeFourierOneOne a t ≫ g)
    (h2 : oneKoszulCubeFourierOneTwo a t ≫ f = oneKoszulCubeFourierOneTwo a t ≫ g)
    : f = g := by
  apply oneKoszulCubeXNegOne_hom_ext a
  · simp only [oneKoszulCubeE0_fourier a t ht, add_comp,
      h0, h1, h2]
  · simp only [oneKoszulCubeE1_fourier a t ht, add_comp,
      Linear.smul_comp, h0, h1, h2]
  · simp only [oneKoszulCubeE2_fourier a t ht, add_comp,
      Linear.smul_comp, h0, h1, h2]
lemma oneKoszulCubeFourierTwo_hom_ext (a t : R) (ht : t ^ 2 + t + 1 = 0)
    {Y : ModuleCat.{u} R} {f g : (tensorCube (oneKoszulComplex a)).X (-2) ⟶ Y}
    (h0 : oneKoszulCubeFourierTwo01 a t ≫ f = oneKoszulCubeFourierTwo01 a t ≫ g)
    (h1 : oneKoszulCubeFourierTwo02 a t ≫ f = oneKoszulCubeFourierTwo02 a t ≫ g)
    (h2 : oneKoszulCubeFourierTwo12 a t ≫ f = oneKoszulCubeFourierTwo12 a t ≫ g)
    : f = g := by
  apply oneKoszulCubeXNegTwo_hom_ext a
  · simp only [oneKoszulCubeE01_fourier a t ht, add_comp, sub_comp,
      Linear.smul_comp, h0, h1, h2]
  · simp only [oneKoszulCubeE02_fourier a t ht, add_comp,
      Linear.smul_comp, h0, h1, h2]
  · simp only [oneKoszulCubeE12_fourier a t ht, add_comp, sub_comp,
      Linear.smul_comp, h0, h1, h2]
lemma oneKoszulCubeFourierTop_hom_ext (a t : R) (ht : t ^ 2 + t + 1 = 0)
    {Y : ModuleCat.{u} R} {f g : (tensorCube (oneKoszulComplex a)).X (-3) ⟶ Y}
    (h : oneKoszulCubeFourierTop a t ≫ f = oneKoszulCubeFourierTop a t ≫ g) : f = g := by
  apply oneKoszulCubeXNegThree_hom_ext a
  simp only [oneKoszulCubeTop_fourier a t ht, Linear.smul_comp, h]

end Adams
end SerrePositivity

end KoszulCubeFourierBasisPart

section KoszulShiftTwoModelPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex CochainComplex
variable {R : Type u} [CommRing R]
namespace Adams

abbrev oneKoszulShiftTwo (a : R) := (oneKoszulComplex a)⟦(2 : ℤ)⟧

def oneKoszulShiftTwoXNegTwoIso (a : R) :
    (oneKoszulShiftTwo a).X (-2) ≅ ModuleCat.of R R :=
  (oneKoszulComplex a).shiftFunctorObjXIso 2 (-2) 0 (by omega) ≪≫ oneKoszulXZeroIso a

def oneKoszulShiftTwoXNegThreeIso (a : R) :
    (oneKoszulShiftTwo a).X (-3) ≅ ModuleCat.of R R :=
  (oneKoszulComplex a).shiftFunctorObjXIso 2 (-3) (-1) (by omega) ≪≫ oneKoszulXNegOneIso a

lemma oneKoszulShiftTwo_isZero_X_other (a : R) (n : ℤ) (hn : n ≠ -3 ∧ n ≠ -2) :
    IsZero ((oneKoszulShiftTwo a).X n) :=
  (oneKoszul_isZero_X_other a (n + 2) (by omega)).of_iso
    ((oneKoszulComplex a).shiftFunctorObjXIso 2 n (n + 2) rfl)

lemma oneKoszulShiftTwo_generator_d (a : R) :
    (oneKoszulShiftTwoXNegThreeIso a).inv ≫ (oneKoszulShiftTwo a).d (-3) (-2) =
      a • (oneKoszulShiftTwoXNegTwoIso a).inv := by
  change (oneKoszulXNegOneIso a).inv ≫
    ((2 : ℤ).negOnePow • (oneKoszulComplex a).d (-1) 0) = _
  rw [show (2 : ℤ).negOnePow = 1 from Int.negOnePow_two_mul 1, one_smul,
    oneKoszul_generator_d]
  rfl

end Adams
end SerrePositivity

end KoszulShiftTwoModelPart

section KoszulCubeFourierEmbeddingsPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
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

end KoszulCubeFourierEmbeddingsPart
