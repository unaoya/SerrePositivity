module

public import SerrePositivity.KTheory.Adams.KoszulCubeFourier
public import SerrePositivity.PerfectComplex.BiproductPerfect
public import SerrePositivity.PerfectComplex.ClosedSupport.Functoriality
public import SerrePositivity.PerfectComplex.Eigen.Cubic
public import SerrePositivity.PerfectComplex.KoszulClasses
public import SerrePositivity.PerfectComplex.Eigen.CubicClass

/-! # 四つのシフトの Fourier モデル

## 概要

四つのシフトを足した Fourier モデルと、Koszul 三乗への同変な写像、その同次生成元と次数ごとの逆写像を与え、同変な鎖の同型であることを示す。二段シフトした一元 Koszul 複体の閉台の類と、Fourier モデルの重み付きの指標の類を計算する。

## 方針

次数ごとの逆写像を明示して同型を示す。

## 規約

`KoszulShiftTwoClass` は Fourier モデルの類の計算にだけ使うのでここに置く。

## 使われ方

`Adams/CyclicThree` の Koszul の正規化。
-/

@[expose] public noncomputable section

universe u v

section KoszulCubeFourierModelMapPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex Preadditive
variable {R : Type u} [CommRing R]
namespace Adams

abbrev oneKoszulCubeFourierModel (a : R) :=
  oneKoszulComplex a ⊞
    (oneKoszulShiftOne a ⊞ (oneKoszulShiftOne a ⊞ oneKoszulShiftTwo a))

def oneKoszulCubeFourierModelRotation (a t : R) :
    oneKoszulCubeFourierModel a ⟶ oneKoszulCubeFourierModel a :=
  biprod.map (𝟙 _) (biprod.map (t • 𝟙 _) (biprod.map (t ^ 2 • 𝟙 _) (𝟙 _)))

/-- The four scalar actions, using character zero on the two even shifts. -/
def oneKoszulCubeFourierScalarAction (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    CochainCubicAction (oneKoszulCubeFourierModel a) :=
  let action (K : CochainComplex (ModuleCat.{u} R) ℤ) (j : Fin 3) :=
    CochainCubicAction.characterScalar K t (cube_eq_one_of_cubic_relation t ht) j
  (action (oneKoszulComplex a) 0).biprod
    ((action (oneKoszulShiftOne a) 1).biprod
      ((action (oneKoszulShiftOne a) 2).biprod (action (oneKoszulShiftTwo a) 0)))

lemma oneKoszulCubeFourierModelRotation_cube (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierModelRotation a t ≫ oneKoszulCubeFourierModelRotation a t ≫
      oneKoszulCubeFourierModelRotation a t = 𝟙 _ := by
  simpa only [oneKoszulCubeFourierScalarAction, CochainCubicAction.biprod_map,
    CochainCubicAction.characterScalar_map, cubicCharacter, Fin.val_zero, Fin.val_one,
    Fin.val_two, pow_zero, pow_one, one_smul, oneKoszulCubeFourierModelRotation] using
    (oneKoszulCubeFourierScalarAction a t ht).cube

def oneKoszulCubeFourierModelAction (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    CochainCubicAction (oneKoszulCubeFourierModel a) where
  map := oneKoszulCubeFourierModelRotation a t
  cube := oneKoszulCubeFourierModelRotation_cube a t ht

lemma oneKoszulCubeFourierModel_perfect (a : R) :
    strictlyPerfectComplex R (oneKoszulCubeFourierModel a) :=
  strictlyPerfectComplex_biprod (oneKoszulComplex_perfect a)
    (strictlyPerfectComplex_biprod (strictlyPerfectComplex_shift (oneKoszulComplex_perfect a) 1)
      (strictlyPerfectComplex_biprod (strictlyPerfectComplex_shift (oneKoszulComplex_perfect a) 1)
        (strictlyPerfectComplex_shift (oneKoszulComplex_perfect a) 2)))

lemma oneKoszulCubeFourierModel_support (a : R) :
    HasHomologySupportOn (oneKoszulSupport a) (oneKoszulCubeFourierModel a) :=
  (oneKoszulComplex_support a).biprod
    (((oneKoszulComplex_support a).shift 1).biprod
      (((oneKoszulComplex_support a).shift 1).biprod ((oneKoszulComplex_support a).shift 2)))

lemma oneKoszulCubeFourierModel_isZero_X_other (a : R) (n : ℤ)
    (hn : n ≠ -3 ∧ n ≠ -2 ∧ n ≠ -1 ∧ n ≠ 0) :
    IsZero ((oneKoszulCubeFourierModel a).X n) := by
  have hz {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
      (hP : IsZero (P.X n)) (hQ : IsZero (Q.X n)) : IsZero ((P ⊞ Q).X n) :=
    ((biprod_isZero_iff _ _).mpr ⟨hP, hQ⟩).of_iso (biprodXIso P Q n)
  exact hz (oneKoszul_isZero_X_other a n (by omega))
    (hz (oneKoszulShiftOne_isZero_X_other a n (by omega))
      (hz (oneKoszulShiftOne_isZero_X_other a n (by omega))
        (oneKoszulShiftTwo_isZero_X_other a n (by omega))))

variable [Invertible (3 : R)]

def oneKoszulCubeFourierModelMap (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierModel a ⟶ tensorCube (oneKoszulComplex a) :=
  biprod.desc (oneKoszulCubeFourierZeroEmbedding a)
    (biprod.desc (oneKoszulCubeFourierOneEmbedding a t ht)
      (biprod.desc (oneKoszulCubeFourierTwoEmbedding a t ht)
        (oneKoszulCubeFourierTopEmbedding a t)))

lemma oneKoszulCubeFourierModelMap_rotation (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierModelMap a t ht ≫ tensorCubeRotation (oneKoszulComplex a) =
      oneKoszulCubeFourierModelRotation a t ≫ oneKoszulCubeFourierModelMap a t ht := by
  apply biprod.hom_ext'
  · simp [oneKoszulCubeFourierModelMap, oneKoszulCubeFourierModelRotation,
      oneKoszulCubeFourierZeroEmbedding_rotation]
  · apply biprod.hom_ext'
    · simp [oneKoszulCubeFourierModelMap, oneKoszulCubeFourierModelRotation,
        Linear.smul_comp, oneKoszulCubeFourierOneEmbedding_rotation a t ht]
    · apply biprod.hom_ext'
      · simp [oneKoszulCubeFourierModelMap, oneKoszulCubeFourierModelRotation,
          Linear.smul_comp, oneKoszulCubeFourierTwoEmbedding_rotation a t ht]
      · simp [oneKoszulCubeFourierModelMap, oneKoszulCubeFourierModelRotation,
          oneKoszulCubeFourierTopEmbedding_rotation]

end Adams
end SerrePositivity

end KoszulCubeFourierModelMapPart

section KoszulCubeFourierModelGeneratorsPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex Preadditive
variable {R : Type u} [CommRing R]
namespace Adams

abbrev oneKoszulCubeFourierModelTail (a : R) :=
  oneKoszulShiftOne a ⊞ (oneKoszulShiftOne a ⊞ oneKoszulShiftTwo a)

abbrev oneKoszulCubeFourierModelInZero (a : R) :
    oneKoszulComplex a ⟶ oneKoszulCubeFourierModel a := biprod.inl

abbrev oneKoszulCubeFourierModelInOne (a : R) :
    oneKoszulShiftOne a ⟶ oneKoszulCubeFourierModel a :=
  (biprod.inl : oneKoszulShiftOne a ⟶ oneKoszulCubeFourierModelTail a) ≫ biprod.inr

abbrev oneKoszulCubeFourierModelInTwo (a : R) :
    oneKoszulShiftOne a ⟶ oneKoszulCubeFourierModel a :=
  (biprod.inl : oneKoszulShiftOne a ⟶ oneKoszulShiftOne a ⊞ oneKoszulShiftTwo a) ≫
    (biprod.inr : _ ⟶ oneKoszulCubeFourierModelTail a) ≫ biprod.inr

abbrev oneKoszulCubeFourierModelInTop (a : R) :
    oneKoszulShiftTwo a ⟶ oneKoszulCubeFourierModel a :=
  (biprod.inr : oneKoszulShiftTwo a ⟶ oneKoszulShiftOne a ⊞ oneKoszulShiftTwo a) ≫
    (biprod.inr : _ ⟶ oneKoszulCubeFourierModelTail a) ≫ biprod.inr

variable [Invertible (3 : R)]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierModelInZero_map (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierModelInZero a ≫ oneKoszulCubeFourierModelMap a t ht =
      oneKoszulCubeFourierZeroEmbedding a := by
  simp [oneKoszulCubeFourierModelMap]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierModelInOne_map (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierModelInOne a ≫ oneKoszulCubeFourierModelMap a t ht =
      oneKoszulCubeFourierOneEmbedding a t ht := by
  simp [oneKoszulCubeFourierModelMap, Category.assoc]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierModelInTwo_map (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierModelInTwo a ≫ oneKoszulCubeFourierModelMap a t ht =
      oneKoszulCubeFourierTwoEmbedding a t ht := by
  simp [oneKoszulCubeFourierModelMap, Category.assoc]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierModelInTop_map (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierModelInTop a ≫ oneKoszulCubeFourierModelMap a t ht =
      oneKoszulCubeFourierTopEmbedding a t := by
  simp [oneKoszulCubeFourierModelMap, Category.assoc]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierModelZeroLower_map (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (oneKoszulXNegOneIso a).inv ≫ (oneKoszulCubeFourierModelInZero a).f (-1) ≫
      (oneKoszulCubeFourierModelMap a t ht).f (-1) = oneKoszulCubeFourierOneZero a := by
  rw [← HomologicalComplex.comp_f, oneKoszulCubeFourierModelInZero_map]
  simp [oneKoszulCubeFourierZeroEmbedding, cochainTwoTermScalarMap,
    cochainTwoTermScalarMapX]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierModelZeroUpper_map (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (oneKoszulXZeroIso a).inv ≫ (oneKoszulCubeFourierModelInZero a).f (0) ≫
      (oneKoszulCubeFourierModelMap a t ht).f (0) = oneKoszulCubeBottom a := by
  rw [← HomologicalComplex.comp_f, oneKoszulCubeFourierModelInZero_map]
  simp [oneKoszulCubeFourierZeroEmbedding, cochainTwoTermScalarMap,
    cochainTwoTermScalarMapX]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierModelOneLower_map (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (oneKoszulShiftOneXNegTwoIso a).inv ≫ (oneKoszulCubeFourierModelInOne a).f (-2) ≫
      (oneKoszulCubeFourierModelMap a t ht).f (-2) = -oneKoszulCubeFourierTwo01 a t := by
  rw [← HomologicalComplex.comp_f, oneKoszulCubeFourierModelInOne_map]
  simp [oneKoszulCubeFourierOneEmbedding, cochainTwoTermScalarMap,
    cochainTwoTermScalarMapX]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierModelOneUpper_map (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (oneKoszulShiftOneXNegOneIso a).inv ≫ (oneKoszulCubeFourierModelInOne a).f (-1) ≫
      (oneKoszulCubeFourierModelMap a t ht).f (-1) = oneKoszulCubeFourierOneOne a t := by
  rw [← HomologicalComplex.comp_f, oneKoszulCubeFourierModelInOne_map]
  simp [oneKoszulCubeFourierOneEmbedding, cochainTwoTermScalarMap,
    cochainTwoTermScalarMapX]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierModelTwoLower_map (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (oneKoszulShiftOneXNegTwoIso a).inv ≫ (oneKoszulCubeFourierModelInTwo a).f (-2) ≫
      (oneKoszulCubeFourierModelMap a t ht).f (-2) = -oneKoszulCubeFourierTwo02 a t := by
  rw [← HomologicalComplex.comp_f, oneKoszulCubeFourierModelInTwo_map]
  simp [oneKoszulCubeFourierTwoEmbedding, cochainTwoTermScalarMap,
    cochainTwoTermScalarMapX]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierModelTwoUpper_map (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (oneKoszulShiftOneXNegOneIso a).inv ≫ (oneKoszulCubeFourierModelInTwo a).f (-1) ≫
      (oneKoszulCubeFourierModelMap a t ht).f (-1) = oneKoszulCubeFourierOneTwo a t := by
  rw [← HomologicalComplex.comp_f, oneKoszulCubeFourierModelInTwo_map]
  simp [oneKoszulCubeFourierTwoEmbedding, cochainTwoTermScalarMap,
    cochainTwoTermScalarMapX]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierModelTopLower_map (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (oneKoszulShiftTwoXNegThreeIso a).inv ≫ (oneKoszulCubeFourierModelInTop a).f (-3) ≫
      (oneKoszulCubeFourierModelMap a t ht).f (-3) = oneKoszulCubeFourierTop a t := by
  rw [← HomologicalComplex.comp_f, oneKoszulCubeFourierModelInTop_map]
  simp [oneKoszulCubeFourierTopEmbedding, cochainTwoTermScalarMap,
    cochainTwoTermScalarMapX]

@[reassoc (attr := simp)]
lemma oneKoszulCubeFourierModelTopUpper_map (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (oneKoszulShiftTwoXNegTwoIso a).inv ≫ (oneKoszulCubeFourierModelInTop a).f (-2) ≫
      (oneKoszulCubeFourierModelMap a t ht).f (-2) = oneKoszulCubeFourierTwo12 a t := by
  rw [← HomologicalComplex.comp_f, oneKoszulCubeFourierModelInTop_map]
  simp [oneKoszulCubeFourierTopEmbedding, cochainTwoTermScalarMap,
    cochainTwoTermScalarMapX]

end Adams
end SerrePositivity

end KoszulCubeFourierModelGeneratorsPart

section KoszulCubeFourierModelInversePart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex Preadditive
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace Adams

omit [Invertible (3 : R)] in
lemma oneKoszulCubeFourierModelX_hom_ext (a : R) (n : ℤ) {M : ModuleCat.{u} R}
    {f g : (oneKoszulCubeFourierModel a).X n ⟶ M}
    (h0 : (oneKoszulCubeFourierModelInZero a).f n ≫ f =
      (oneKoszulCubeFourierModelInZero a).f n ≫ g)
    (h1 : (oneKoszulCubeFourierModelInOne a).f n ≫ f =
      (oneKoszulCubeFourierModelInOne a).f n ≫ g)
    (h2 : (oneKoszulCubeFourierModelInTwo a).f n ≫ f =
      (oneKoszulCubeFourierModelInTwo a).f n ≫ g)
    (h3 : (oneKoszulCubeFourierModelInTop a).f n ≫ f =
      (oneKoszulCubeFourierModelInTop a).f n ≫ g) : f = g := by
  apply biprodX_ext_from h0
  apply biprodX_ext_from
  · simpa only [oneKoszulCubeFourierModelInOne, comp_f, Category.assoc] using h1
  · apply biprodX_ext_from
    · simpa only [oneKoszulCubeFourierModelInTwo, comp_f, Category.assoc] using h2
    · simpa only [oneKoszulCubeFourierModelInTop, comp_f, Category.assoc] using h3

def oneKoszulCubeFourierModelInverseZero (a _t : R) :
    (tensorCube (oneKoszulComplex a)).X (0) ⟶ (oneKoszulCubeFourierModel a).X (0) :=
  oneKoszulCubeBottomCoordinate a ≫
    (oneKoszulXZeroIso a).inv ≫ (oneKoszulCubeFourierModelInZero a).f (0)

lemma oneKoszulCubeFourierModelInverseZero_map (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierModelInverseZero a t ≫ (oneKoszulCubeFourierModelMap a t ht).f (0) =
      𝟙 _ := by
  apply oneKoszulCubeXZero_hom_ext a
  all_goals simp only [oneKoszulCubeFourierModelInverseZero, Category.assoc]
  all_goals simp only [oneKoszulCubeFourierModelZeroUpper_map a t ht]
  all_goals simp

def oneKoszulCubeFourierModelInverseNegOne (a t : R) :
    (tensorCube (oneKoszulComplex a)).X (-1) ⟶ (oneKoszulCubeFourierModel a).X (-1) :=
  oneKoszulCubeFourierOneZeroCoordinate a ≫
      (oneKoszulXNegOneIso a).inv ≫ (oneKoszulCubeFourierModelInZero a).f (-1) +
    oneKoszulCubeFourierOneOneCoordinate a t ≫
      (oneKoszulShiftOneXNegOneIso a).inv ≫ (oneKoszulCubeFourierModelInOne a).f (-1) +
    oneKoszulCubeFourierOneTwoCoordinate a t ≫
      (oneKoszulShiftOneXNegOneIso a).inv ≫ (oneKoszulCubeFourierModelInTwo a).f (-1)

lemma oneKoszulCubeFourierModelInverseNegOne_map (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierModelInverseNegOne a t ≫ (oneKoszulCubeFourierModelMap a t ht).f (-1) =
      𝟙 _ := by
  apply oneKoszulCubeFourierOne_hom_ext a t ht
  all_goals simp only [oneKoszulCubeFourierModelInverseNegOne, Category.assoc,
    comp_add, add_comp]
  all_goals simp only [oneKoszulCubeFourierModelZeroLower_map a t ht,
    oneKoszulCubeFourierModelOneUpper_map a t ht,
    oneKoszulCubeFourierModelTwoUpper_map a t ht]
  all_goals simp [ht]

def oneKoszulCubeFourierModelInverseNegTwo (a t : R) :
    (tensorCube (oneKoszulComplex a)).X (-2) ⟶ (oneKoszulCubeFourierModel a).X (-2) :=
  (-oneKoszulCubeFourierTwo01Coordinate a t) ≫
      (oneKoszulShiftOneXNegTwoIso a).inv ≫ (oneKoszulCubeFourierModelInOne a).f (-2) +
    (-oneKoszulCubeFourierTwo02Coordinate a t) ≫
      (oneKoszulShiftOneXNegTwoIso a).inv ≫ (oneKoszulCubeFourierModelInTwo a).f (-2) +
    oneKoszulCubeFourierTwo12Coordinate a t ≫
      (oneKoszulShiftTwoXNegTwoIso a).inv ≫ (oneKoszulCubeFourierModelInTop a).f (-2)

lemma oneKoszulCubeFourierModelInverseNegTwo_map (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierModelInverseNegTwo a t ≫ (oneKoszulCubeFourierModelMap a t ht).f (-2) =
      𝟙 _ := by
  apply oneKoszulCubeFourierTwo_hom_ext a t ht
  all_goals simp only [oneKoszulCubeFourierModelInverseNegTwo, Category.assoc,
    comp_add, add_comp, neg_comp, comp_neg]
  all_goals simp only [oneKoszulCubeFourierModelOneLower_map a t ht,
    oneKoszulCubeFourierModelTwoLower_map a t ht,
    oneKoszulCubeFourierModelTopUpper_map a t ht]
  all_goals simp [ht]

def oneKoszulCubeFourierModelInverseNegThree (a t : R) :
    (tensorCube (oneKoszulComplex a)).X (-3) ⟶ (oneKoszulCubeFourierModel a).X (-3) :=
  oneKoszulCubeFourierTopCoordinate a t ≫
      (oneKoszulShiftTwoXNegThreeIso a).inv ≫ (oneKoszulCubeFourierModelInTop a).f (-3)

lemma oneKoszulCubeFourierModelInverseNegThree_map (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierModelInverseNegThree a t ≫ (oneKoszulCubeFourierModelMap a t ht).f (-3) =
      𝟙 _ := by
  apply oneKoszulCubeFourierTop_hom_ext a t ht
  all_goals simp only [oneKoszulCubeFourierModelInverseNegThree, Category.assoc]
  all_goals simp only [oneKoszulCubeFourierModelTopLower_map a t ht]
  all_goals simp [ht]

lemma oneKoszulCubeFourierModelMap_inverseZero (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (oneKoszulCubeFourierModelMap a t ht).f (0) ≫ oneKoszulCubeFourierModelInverseZero a t =
      𝟙 _ := by
  apply oneKoszulCubeFourierModelX_hom_ext a (0)
  · apply (cancel_epi (oneKoszulXZeroIso a).inv).mp
    simp only [oneKoszulCubeFourierModelZeroUpper_map_assoc a t ht]
    simp [oneKoszulCubeFourierModelInverseZero]
  · exact (oneKoszulShiftOne_isZero_X_other a (0) (by omega)).eq_of_src _ _
  · exact (oneKoszulShiftOne_isZero_X_other a (0) (by omega)).eq_of_src _ _
  · exact (oneKoszulShiftTwo_isZero_X_other a (0) (by omega)).eq_of_src _ _

lemma oneKoszulCubeFourierModelMap_inverseNegOne (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (oneKoszulCubeFourierModelMap a t ht).f (-1) ≫ oneKoszulCubeFourierModelInverseNegOne a t =
      𝟙 _ := by
  apply oneKoszulCubeFourierModelX_hom_ext a (-1)
  · apply (cancel_epi (oneKoszulXNegOneIso a).inv).mp
    simp only [oneKoszulCubeFourierModelZeroLower_map_assoc a t ht]
    simp [oneKoszulCubeFourierModelInverseNegOne, comp_add, ht]
  · apply (cancel_epi (oneKoszulShiftOneXNegOneIso a).inv).mp
    simp only [oneKoszulCubeFourierModelOneUpper_map_assoc a t ht]
    simp [oneKoszulCubeFourierModelInverseNegOne, comp_add, ht]
  · apply (cancel_epi (oneKoszulShiftOneXNegOneIso a).inv).mp
    simp only [oneKoszulCubeFourierModelTwoUpper_map_assoc a t ht]
    simp [oneKoszulCubeFourierModelInverseNegOne, comp_add, ht]
  · exact (oneKoszulShiftTwo_isZero_X_other a (-1) (by omega)).eq_of_src _ _

lemma oneKoszulCubeFourierModelMap_inverseNegTwo (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (oneKoszulCubeFourierModelMap a t ht).f (-2) ≫ oneKoszulCubeFourierModelInverseNegTwo a t =
      𝟙 _ := by
  apply oneKoszulCubeFourierModelX_hom_ext a (-2)
  · exact (oneKoszul_isZero_X_other a (-2) (by omega)).eq_of_src _ _
  · apply (cancel_epi (oneKoszulShiftOneXNegTwoIso a).inv).mp
    simp only [oneKoszulCubeFourierModelOneLower_map_assoc a t ht]
    simp [oneKoszulCubeFourierModelInverseNegTwo, comp_add, neg_comp, comp_neg, ht]
  · apply (cancel_epi (oneKoszulShiftOneXNegTwoIso a).inv).mp
    simp only [oneKoszulCubeFourierModelTwoLower_map_assoc a t ht]
    simp [oneKoszulCubeFourierModelInverseNegTwo, comp_add, neg_comp, comp_neg, ht]
  · apply (cancel_epi (oneKoszulShiftTwoXNegTwoIso a).inv).mp
    simp only [oneKoszulCubeFourierModelTopUpper_map_assoc a t ht]
    simp [oneKoszulCubeFourierModelInverseNegTwo, comp_add, neg_comp, comp_neg, ht]

lemma oneKoszulCubeFourierModelMap_inverseNegThree (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (oneKoszulCubeFourierModelMap a t ht).f (-3) ≫ oneKoszulCubeFourierModelInverseNegThree a t =
      𝟙 _ := by
  apply oneKoszulCubeFourierModelX_hom_ext a (-3)
  · exact (oneKoszul_isZero_X_other a (-3) (by omega)).eq_of_src _ _
  · exact (oneKoszulShiftOne_isZero_X_other a (-3) (by omega)).eq_of_src _ _
  · exact (oneKoszulShiftOne_isZero_X_other a (-3) (by omega)).eq_of_src _ _
  · apply (cancel_epi (oneKoszulShiftTwoXNegThreeIso a).inv).mp
    simp only [oneKoszulCubeFourierModelTopLower_map_assoc a t ht]
    simp [oneKoszulCubeFourierModelInverseNegThree, ht]

end Adams
end SerrePositivity

end KoszulCubeFourierModelInversePart

section KoszulCubeFourierModelIsoPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace Adams

instance oneKoszulCubeFourierModelMap_f_isIso (a t : R) (ht : t ^ 2 + t + 1 = 0)
    (n : ℤ) : IsIso ((oneKoszulCubeFourierModelMap a t ht).f n) := by
  by_cases hnZero : n = 0
  · subst n
    exact ⟨⟨oneKoszulCubeFourierModelInverseZero a t,
      oneKoszulCubeFourierModelMap_inverseZero a t ht,
      oneKoszulCubeFourierModelInverseZero_map a t ht⟩⟩
  by_cases hnNegOne : n = -1
  · subst n
    exact ⟨⟨oneKoszulCubeFourierModelInverseNegOne a t,
      oneKoszulCubeFourierModelMap_inverseNegOne a t ht,
      oneKoszulCubeFourierModelInverseNegOne_map a t ht⟩⟩
  by_cases hnNegTwo : n = -2
  · subst n
    exact ⟨⟨oneKoszulCubeFourierModelInverseNegTwo a t,
      oneKoszulCubeFourierModelMap_inverseNegTwo a t ht,
      oneKoszulCubeFourierModelInverseNegTwo_map a t ht⟩⟩
  by_cases hnNegThree : n = -3
  · subst n
    exact ⟨⟨oneKoszulCubeFourierModelInverseNegThree a t,
      oneKoszulCubeFourierModelMap_inverseNegThree a t ht,
      oneKoszulCubeFourierModelInverseNegThree_map a t ht⟩⟩
  have hn : n ≠ -3 ∧ n ≠ -2 ∧ n ≠ -1 ∧ n ≠ 0 := by omega
  have hD := oneKoszulCubeFourierModel_isZero_X_other a n hn
  have hK := oneKoszulCube_isZero_X_other a n hn
  rw [hD.eq_of_src ((oneKoszulCubeFourierModelMap a t ht).f n) 0]
  exact (isIsoZero_iff_source_target_isZero _ _).mpr ⟨hD, hK⟩

instance oneKoszulCubeFourierModelMap_isIso (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    IsIso (oneKoszulCubeFourierModelMap a t ht) :=
  HomologicalComplex.Hom.isIso_of_components _

def oneKoszulCubeFourierModelIso (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierModel a ≅ tensorCube (oneKoszulComplex a) :=
  asIso (oneKoszulCubeFourierModelMap a t ht)

@[simp]
lemma oneKoszulCubeFourierModelIso_hom (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (oneKoszulCubeFourierModelIso a t ht).hom = oneKoszulCubeFourierModelMap a t ht := rfl

lemma oneKoszulCubeFourierModelIso_rotation (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    (oneKoszulCubeFourierModelIso a t ht).hom ≫ tensorCubeRotation (oneKoszulComplex a) =
      (oneKoszulCubeFourierModelAction a t ht).map ≫
        (oneKoszulCubeFourierModelIso a t ht).hom :=
  oneKoszulCubeFourierModelMap_rotation a t ht

end Adams
end SerrePositivity

end KoszulCubeFourierModelIsoPart

section KoszulShiftTwoClassPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits HomologicalComplex
variable {R : Type u} [CommRing R]
namespace Adams

lemma oneKoszulShiftTwo_class (a : R) :
    K0WithSupport.mk (oneKoszulSupport a) (supportedPerfectOnObj (oneKoszulSupport a)
      (oneKoszulShiftTwo a) (strictlyPerfectComplex_shift (oneKoszulComplex_perfect a) 2)
      ((oneKoszulComplex_support a).shift 2)) = oneKoszulClass a := by
  let hp := strictlyPerfectComplex_shift (oneKoszulComplex_perfect a) 1
  let hs := (oneKoszulComplex_support a).shift 1
  have hχ : ClosedSupportShortExactAdditive (oneKoszulSupport a)
      (K0WithSupport.mk (oneKoszulSupport a)) := K0WithSupport.mk_shortExact (oneKoszulSupport a)
  have h2 := hχ.shift_one (fun e => K0WithSupport.mk_iso (oneKoszulSupport a) e)
    ((oneKoszulComplex a)⟦(1 : ℤ)⟧) hp hs
  have he := K0WithSupport.mk_eq_of_quasiIso (oneKoszulSupport a)
    (oneKoszulShiftTwo a) (((oneKoszulComplex a)⟦(1 : ℤ)⟧)⟦(1 : ℤ)⟧)
    (strictlyPerfectComplex_shift (oneKoszulComplex_perfect a) 2)
    (strictlyPerfectComplex_shift hp 1) ((oneKoszulComplex_support a).shift 2) (hs.shift 1)
    ((shiftFunctorAdd' (CochainComplex (ModuleCat.{u} R) ℤ)
      (1 : ℤ) 1 2 (by norm_num)).app (oneKoszulComplex a)).hom
  rw [he, h2, oneKoszulClass_shift_one, neg_neg]

end Adams
end SerrePositivity

end KoszulShiftTwoClassPart

section KoszulCubeFourierModelClassPart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity
open CategoryTheory Category Limits TensorProduct
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace Adams

omit [Invertible (3 : R)] in
lemma oneKoszulCubeFourierModelAction_eq_scalar (a t : R) (ht : t ^ 2 + t + 1 = 0) :
    oneKoszulCubeFourierModelAction a t ht = oneKoszulCubeFourierScalarAction a t ht := by
  apply CochainCubicAction.ext
  simp [oneKoszulCubeFourierModelAction, oneKoszulCubeFourierModelRotation,
    oneKoszulCubeFourierScalarAction, CochainCubicAction.characterScalar,
    cubicCharacter]

lemma oneKoszulCubeFourierModel_weighted_class (E : Type v) [CommRing E]
    (a t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E) :
    (oneKoszulCubeFourierModelAction a t ht).weightedK0Class E t ht ζ
      (oneKoszulSupport a) (oneKoszulCubeFourierModel_perfect a)
      (oneKoszulCubeFourierModel_support a) =
      ((2 : E) - ζ - ζ ^ 2) • ((1 : E) ⊗ₜ[ℤ] oneKoszulClass a) := by
  let hp0 := oneKoszulComplex_perfect a
  let hp1 := strictlyPerfectComplex_shift hp0 1
  let hp2 := strictlyPerfectComplex_shift hp0 2
  let hs0 := oneKoszulComplex_support a
  let hs1 := hs0.shift 1
  let hs2 := hs0.shift 2
  rw [oneKoszulCubeFourierModelAction_eq_scalar]
  unfold oneKoszulCubeFourierScalarAction
  rw [CochainCubicAction.weightedK0Class_biprod E _ _ t ht ζ (oneKoszulSupport a)
    hp0 (strictlyPerfectComplex_biprod hp1 (strictlyPerfectComplex_biprod hp1 hp2))
    hs0 (hs1.biprod (hs1.biprod hs2))]
  rw [CochainCubicAction.weightedK0Class_biprod E _ _ t ht ζ (oneKoszulSupport a)
    hp1 (strictlyPerfectComplex_biprod hp1 hp2) hs1 (hs1.biprod hs2)]
  rw [CochainCubicAction.weightedK0Class_biprod E _ _ t ht ζ (oneKoszulSupport a)
    hp1 hp2 hs1 hs2]
  simp only [CochainCubicAction.weightedK0Class_characterScalar]
  rw [oneKoszulClass_shift_one a, oneKoszulShiftTwo_class a]
  change cubicCharacter ζ 0 ⊗ₜ[ℤ] oneKoszulClass a +
    (cubicCharacter ζ 1 ⊗ₜ[ℤ] (-oneKoszulClass a) +
      (cubicCharacter ζ 2 ⊗ₜ[ℤ] (-oneKoszulClass a) +
        cubicCharacter ζ 0 ⊗ₜ[ℤ] oneKoszulClass a)) = _
  simp only [cubicCharacter, Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one,
    tmul_neg, sub_smul, two_smul, smul_tmul', smul_eq_mul, mul_one]
  abel

end Adams
end SerrePositivity

end KoszulCubeFourierModelClassPart
