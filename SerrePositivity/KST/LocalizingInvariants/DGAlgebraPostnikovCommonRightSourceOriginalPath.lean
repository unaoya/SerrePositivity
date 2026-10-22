module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightBaseGlue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCellImageRelative
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightZeroDiagram

/-!
概要：元の S 経路と B 遷移後の持ち上げの全射を、元の ImageWitness で表示する。
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

lemma postnikovCommonRightFixedSource_original_hom :
    (postnikovCommonRightFixedSourceRelative R f c d).hom =
    cellPathNonpositiveToDoubleCell R (postnikovCommonClassBase R f c d) ≫
      (postnikovCellImageRelative R (B.obj d.zero.stage).obj (B.obj i).obj
        (postnikovCommonClassBase R f c d) 1 (by omega)
        (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator
        (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom).hom ≫
      Path.map R (SquareZero.baseChangeMap (postnikovCommonRightDenBase R f c d)
        (postnikovShiftedLayerBimodule R (B.obj i).obj 1 (by omega) 1) ≫
          postnikovClassToZeroBase R (B.obj i).obj 1 (by omega) 1) := by
  change ((cellPathNonpositiveToDoubleCell R (postnikovCommonClassBase R f c d) ≫
    ((postnikovCellImageRelative R (B.obj d.zero.stage).obj (B.obj i).obj
      (postnikovCommonClassBase R f c d) 1 (by omega)
      (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator
        (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom).hom ≫
      Path.map R (postnikovCommonRightDenClassIso R f c d).hom)) ≫
      Path.map R (postnikovCommonRightClassToZero R f c d)) = _
  simp only [Category.assoc, ← Path.map_comp, postnikovCommonRightDenClassIso_zero]

variable {j : ℕ} (hj : j ≤ i)

lemma postnikovCommonRightSourceTransition_original_map :
    (postnikovCommonRightTransitionLift R f c d hj
      (postnikovCommonRightFixedSourceRelative R f c d)).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) =
    cellAugmentation R (postnikovCommonRightCellSource R f c d) ≫
      cellPathNonpositiveToDoubleCell R (postnikovCommonClassBase R f c d) ≫
      (postnikovCellImageRelative R (B.obj d.zero.stage).obj (B.obj i).obj
        (postnikovCommonClassBase R f c d) 1 (by omega)
        (postnikovOneRoofRefine R f c d.zero.source_le).roof.denominator
        (B.transition (d.zero.inverse_le.trans d.zero.stage_le)).hom).hom ≫
      Path.map R (SquareZero.baseChangeMap (postnikovCommonRightDenBase R f c d)
        (postnikovShiftedLayerBimodule R (B.obj i).obj 1 (by omega) 1) ≫
          postnikovClassToZeroBase R (B.obj i).obj 1 (by omega) 1) ≫
        Path.map R (postnikovZeroClassMap R 1 1 (B.transition hj).hom) := by
  rw [postnikovCommonRightTransitionLift_map R f c d hj
    (postnikovCommonRightFixedSourceRelative R f c d),
    postnikovCommonRightFixedSource_original_hom R f c d]
  simp only [Category.assoc]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
