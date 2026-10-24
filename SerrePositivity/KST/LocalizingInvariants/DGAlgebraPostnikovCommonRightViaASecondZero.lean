module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightViaAImageMap
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightTargetFirstPath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellImageZeroMap

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightViaASecondZero
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：元の Γ 源上で、A 遷移と fⱼ の零底 affine 第二辺を取り出す。
方針：元の指定細分・ViaA の実係数射を使い、同じ Γ 射影上の相対経路を保つ。
規約：全経路を変更しない。使われ方：fⱼ の元の class 自然性との同定。
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

def postnikovCommonRightViaASecondZeroPath :=
  PostnikovCommonCore.postnikovCommonRightViaASecondZeroPath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightViaASecondZeroPath_map :
    (postnikovCommonRightViaASecondZeroPath R f c d hj).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) =
    postnikovCommonRightImageToSecond R f c d ≫
      (postnikovCellClassOverNaturalityWitness R (A.obj j).obj (B.obj j).obj
        (postnikovCommonClassBase R f c d) 1 (by omega)
        ((postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator ≫
          postnikovMap R (A.transition hj).hom 1) (f.app j).hom).hom ≫
        Path.map R (postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1) :=
  PostnikovCommonCore.postnikovCommonRightViaASecondZeroPath_map
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
