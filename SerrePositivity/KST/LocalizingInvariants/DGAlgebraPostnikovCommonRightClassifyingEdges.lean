module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassZeroNaturality
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightClassifyingBaseContour
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightAffineFixedGlue

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightClassifyingEdges
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：P 上の classifying 正方形の元の中央辺と、既存の三経路貼合せの中央辺を同定する。
方針：零底射の自然性と全二重 class 射影を使う。
規約：元の指定経路全体の厳密等式。使われ方：affine 貼合せの右合成比較。
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

lemma postnikovCommonRightClassifyingBase_zero : postnikovCommonRightClassifyingBase R f c d hj =
    postnikovCommonRightZeroBase R f c d ≫ postnikovMap R (B.transition hj).hom 0 :=
  PostnikovCommonCore.postnikovCommonRightClassifyingBase_zero
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightClassifyingZeroSquare_source_fixed :
    (postnikovCommonRightClassifyingZeroSquare R f c d hj).hom ≫
      Path.source R (Path.algebra R (postnikovZeroClassTarget R (B.obj j).obj 1 1)) =
    cellAugmentation R (postnikovCommonRightCellSource R f c d) ≫
      (postnikovCommonRightFixedCentralRelative R f c d).hom ≫
        Path.map R (postnikovZeroClassMap R 1 1 (B.transition hj).hom) :=
  PostnikovCommonCore.postnikovCommonRightClassifyingZeroSquare_source_fixed
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightClassifyingBaseChangeHom_source_fixed :
    (postnikovCommonRightClassifyingBaseChangeHom R f c d hj ≫
      Path.source R (Path.algebra R (SquareZero.algebra (postnikovCommonClassBase R f c d)
        (bimoduleRestrict (postnikovCommonRightClassifyingBase R f c d hj)
          (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1))))) ≫
      Path.map R (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) =
    cellAugmentation R (postnikovCommonRightCellSource R f c d) ≫
      (postnikovCommonRightFixedCentralRelative R f c d).hom ≫
        Path.map R (postnikovZeroClassMap R 1 1 (B.transition hj).hom) :=
  PostnikovCommonCore.postnikovCommonRightClassifyingBaseChangeHom_source_fixed
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
