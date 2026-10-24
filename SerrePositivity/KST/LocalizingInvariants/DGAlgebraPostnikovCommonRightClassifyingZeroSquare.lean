module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightClassifyingSquare
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightZeroPath

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightClassifyingZeroSquare
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：元の classifying 正方形を零底へ送り、全二重底射影を定数にする。
方針：元の指定右経路の零切断への射影を、非正次数源と零切断の次数境界で同定する。
規約：四隅だけでなく全底経路を保持。使われ方：相対輪郭補正への実入力。
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
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

local instance zeroSquare_apex_nonpositive :
    (postnikovCommonClassBase R f c d).X.IsStrictlyLE 0 :=
  (postnikovOneRoofRefine R f c d.zero.source_le).roof_nonpositive
local instance zeroSquare_target_lowerBound :
    (postnikov R (B.obj j).obj 0).X.IsStrictlyGE 0 := by
  simpa only [neg_zero] using postnikov_lowerBound R (B.obj j).obj 0

/-- 元の cell 細分と右辺から得る同じ零底への射。 -/
def postnikovCommonRightClassifyingZeroProjection :
    cellResolution R (postnikovCommonRightCellSource R f c d) ⟶
      postnikov R (B.obj j).obj 0 :=
  PostnikovCommonCore.postnikovCommonRightClassifyingZeroProjection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightClassifyingZeroSquare : Path.Witness R
    ((cellAugmentation R (postnikovCommonRightCellSource R f c d) ≫
      (postnikovCommonRightFixedCellClassWitness R f c d).hom ≫
        Path.map R (postnikovDerivationTargetMap R (B.transition hj).hom 1 (by omega))) ≫
          Path.map R (postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1))
    ((cellAugmentation R (postnikovCommonRightCellSource R f c d) ≫
      (postnikovCommonRightFixedMappedClassWitness R f c d hj).hom) ≫
        Path.map R (postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1)) :=
  PostnikovCommonCore.postnikovCommonRightClassifyingZeroSquare
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightClassifyingZeroSquare_projection :
    (postnikovCommonRightClassifyingZeroSquare R f c d hj).hom ≫
      Path.map R (Path.map R (SquareZero.projection _ _)) =
    (postnikovCommonRightClassifyingZeroProjection R f c d hj ≫
      Path.diagonal R (postnikov R (B.obj j).obj 0)) ≫
        Path.diagonal R (Path.algebra R (postnikov R (B.obj j).obj 0)) :=
  PostnikovCommonCore.postnikovCommonRightClassifyingZeroSquare_projection
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightClassifyingZeroSquare_source_trace :
    (postnikovCommonRightClassifyingZeroSquare R f c d hj).hom ≫
      Path.map R (Path.source R (SquareZero.algebra (postnikov R (B.obj j).obj 0)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1))) =
    (cellAugmentation R (postnikovCommonRightCellSource R f c d) ≫
      ((postnikovCellClassOverNaturalityWitness R (B.obj i).obj (B.obj j).obj
        (postnikovCommonClassBase R f c d) 1 (by omega)
        (postnikovCommonRightBase R f c d) (B.transition hj).hom).precompNonpositiveCell R).hom) ≫
          Path.map R (postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1) :=
  PostnikovCommonCore.postnikovCommonRightClassifyingZeroSquare_source_trace
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightClassifyingZeroSquare_target_trace :
    (postnikovCommonRightClassifyingZeroSquare R f c d hj).hom ≫
      Path.map R (Path.target R (SquareZero.algebra (postnikov R (B.obj j).obj 0)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1))) =
    (cellAugmentation R (postnikovCommonRightCellSource R f c d) ≫
      ((postnikovCellClassOverNaturalityWitness R (B.obj i).obj (B.obj j).obj
        (postnikovCommonClassBase R f c d) 1 (by omega)
        (postnikovCommonRightDenBase R f c d) (B.transition hj).hom).precompNonpositiveCell
          R).hom) ≫
          Path.map R (postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1) :=
  PostnikovCommonCore.postnikovCommonRightClassifyingZeroSquare_target_trace
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
