module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightShiftedCoefficient
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassEndpoints
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroCoefficientComposition

/-!
概要：元の class の実平方零標的上で、係数逆の右三角形を厳密な可換式へ移す。
方針：同じ共通底上の shift 係数射に平方零関手を適用し、元の class を前合成する。
規約：元の二つの class を結ぶ経路は未主張。使われ方：class の像の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c)

def postnikovCommonRightClassTarget : Mon (Complex R) :=
  SquareZero.algebra (postnikovCommonClassBase R f c d)
    (DGBimoduleShift.obj (postnikovCommonRightLayer R f c d) 1)

def postnikovCommonRightClassNumeratorMap :
    SquareZero.algebra (postnikovCommonClassBase R f c d)
      (postnikovOneRoofShiftedNumeratorLayer R f
        (postnikovOneRoofRefine R f c d.zero.source_le) 1) ⟶
      postnikovCommonRightClassTarget R f c d :=
  SquareZero.coefficientMap _ (postnikovCommonRightShiftedNumeratorMap R f c d 1)

def postnikovCommonRightClassDenominatorMap :
    SquareZero.algebra (postnikovCommonClassBase R f c d)
      (postnikovOneRoofShiftedDenominatorLayer R f
        (postnikovOneRoofRefine R f c d.zero.source_le) 1) ⟶
      postnikovCommonRightClassTarget R f c d :=
  SquareZero.coefficientMap _ (postnikovCommonRightShiftedDenominatorMap R f c d 1)

lemma postnikovCommonRightClass_triangle : postnikovCommonClassCoefficientMap R f c d ≫
    postnikovCommonRightClassNumeratorMap R f c d =
      postnikovCommonRightClassDenominatorMap R f c d :=
  (SquareZero.coefficientMap_comp _ _).trans
    (congrArg (fun t => SquareZero.coefficientMap (postnikovCommonClassBase R f c d) t)
      (postnikovCommonRightShifted_coefficient R f c d 1))

lemma postnikovCommonRightClassNumeratorMap_projection :
    postnikovCommonRightClassNumeratorMap R f c d ≫ SquareZero.projection _ _ =
      SquareZero.projection _ (postnikovOneRoofShiftedNumeratorLayer R f
        (postnikovOneRoofRefine R f c d.zero.source_le) 1) :=
  SquareZero.coefficientMap_projection _ _

lemma postnikovCommonRightClassDenominatorMap_projection :
    postnikovCommonRightClassDenominatorMap R f c d ≫ SquareZero.projection _ _ =
      SquareZero.projection _ (postnikovOneRoofShiftedDenominatorLayer R f
        (postnikovOneRoofRefine R f c d.zero.source_le) 1) :=
  SquareZero.coefficientMap_projection _ _

lemma postnikovCommonClassSource_right_image : postnikovCommonClassSource R f c d ≫
    postnikovCommonRightClassNumeratorMap R f c d =
      postnikovCellClassOver R (B.obj d.zero.stage).obj (postnikovCommonClassBase R f c d)
        1 (by omega) (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator ≫
          postnikovCommonRightClassDenominatorMap R f c d := by
  rw [postnikovCommonClassSource, Category.assoc, postnikovCommonRightClass_triangle]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
