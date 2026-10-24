module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightDenCompositeZero
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightSourceOriginalPath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellImageForwardZero

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightDenFirstPath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：元の Γ 源上で、T の B 遷移後の持ち上げと零底 affine 分母側第一辺を取り出す。
方針：元の指定細分・実係数射を使い、同じ Γ 射影上の相対経路を保つ。
規約：全経路を変更しない。使われ方：二射影の一意性による分母側第一辺の実同定。
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

def postnikovCommonRightSourceRefinedPath :=
  PostnikovCommonCore.postnikovCommonRightSourceRefinedPath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

def postnikovCommonRightDenFirstZeroPath :=
  PostnikovCommonCore.postnikovCommonRightDenFirstZeroPath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightDenFirstZeroPath_map :
    (postnikovCommonRightDenFirstZeroPath R f c d hj).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) =
    postnikovCommonRightImageToSecond R f c d ≫
      (postnikovCellImageForwardRelative R (B.obj d.zero.stage).obj (B.obj i).obj (B.obj j).obj
        (postnikovCommonClassBase R f c d) 1 (by omega)
        (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator
        (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom
      (B.transition hj).hom).hom ≫ Path.map R
      (SquareZero.baseChangeMap
        (((postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator ≫
          postnikovMap R (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom 1) ≫
          postnikovMap R (B.transition hj).hom 1)
        (postnikovShiftedLayerBimodule R (B.obj j).obj 1 (by omega) 1) ≫
          postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1) :=
  PostnikovCommonCore.postnikovCommonRightDenFirstZeroPath_map
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
