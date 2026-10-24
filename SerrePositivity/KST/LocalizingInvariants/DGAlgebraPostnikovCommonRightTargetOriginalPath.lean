module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightBaseGlue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellImageRelative
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightZeroDiagram

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightTargetOriginalPath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：元の T 経路と B 遷移後の持ち上げの全射を、元の ImageWitness で表示する。
方針：元の標的経路の定義と class 標的同型の零底可換式を使う。
規約：端点をそろえて別経路を選ばない。使われ方：affine 第一辺との実照合。
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

lemma postnikovCommonRightFixedTarget_original_hom :
    (postnikovCommonRightFixedTargetRelative R f c d).hom =
    cellPathNonpositiveToDoubleCell R (postnikovCommonClassBase R f c d) ≫
      (postnikovCellImageRelative R (A.obj i).obj (B.obj i).obj
        (postnikovCommonClassBase R f c d) 1 (by omega)
        (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator (f.app i).hom).hom ≫
      Path.map R (SquareZero.baseChangeMap (postnikovCommonRightBase R f c d)
        (postnikovShiftedLayerBimodule R (B.obj i).obj 1 (by omega) 1) ≫
          postnikovClassToZeroBase R (B.obj i).obj 1 (by omega) 1) :=
  PostnikovCommonCore.postnikovCommonRightFixedTarget_original_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

variable {j : ℕ} (hj : j ≤ i)

lemma postnikovCommonRightTargetTransition_original_map :
    (postnikovCommonRightTransitionLift R f c d hj
      (postnikovCommonRightFixedTargetRelative R f c d)).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) =
    cellAugmentation R (postnikovCommonRightCellSource R f c d) ≫
      cellPathNonpositiveToDoubleCell R (postnikovCommonClassBase R f c d) ≫
      (postnikovCellImageRelative R (A.obj i).obj (B.obj i).obj
        (postnikovCommonClassBase R f c d) 1 (by omega)
        (postnikovOneRoofRefine R f c d.zero.source_le).roof.numerator (f.app i).hom).hom ≫
      Path.map R (SquareZero.baseChangeMap (postnikovCommonRightBase R f c d)
        (postnikovShiftedLayerBimodule R (B.obj i).obj 1 (by omega) 1) ≫
          postnikovClassToZeroBase R (B.obj i).obj 1 (by omega) 1) ≫
        Path.map R (postnikovZeroClassMap R 1 1 (B.transition hj).hom) :=
  PostnikovCommonCore.postnikovCommonRightTargetTransition_original_map
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
