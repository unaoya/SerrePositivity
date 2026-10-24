module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightGammaSource
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightContourBottomPath
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovNativeZeroCoefficientIso

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightGammaZeroClass
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：Γ 上の W source の全 class 経路を、既存の零底の輪郭経路へ同定する。
方針：二重経路の底変更と終点評価を可換させ、元の W の全射を回収する。
規約：class の端点だけによる同定を使わない。使われ方：native 模型比較の hk 入力。
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

lemma postnikovCommonRightToClassifying_source :
    postnikovCommonRightToClassifying R f c d ≫
      cellAugmentation R (postnikovCommonRightCellSource R f c d) =
        postnikovCommonRightGammaToSource R f c d :=
  PostnikovCommonCore.postnikovCommonRightToClassifying_source
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c)

lemma postnikovCommonRightContourBottomPath_map :
    (postnikovCommonRightContourBottomPath R f c d hj).hom ≫
      Path.map R (SquareZero.baseChangeMap
        (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) =
    (cellAugmentation R (postnikovCommonRightCellSource R f c d) ≫
      (postnikovCommonRightFixedMappedClassWitness R f c d hj).hom) ≫
        Path.map R (postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1) :=
  PostnikovCommonCore.postnikovCommonRightContourBottomPath_map
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightGammaSourceWitness_zeroClass :
    ((postnikovCommonRightGammaSourceWitness R f c d hj).hom ≫
      Path.map R (postnikovPerturbedClass R (B.obj j).obj 1 (by omega))) ≫
        Path.map R (postnikovClassToZeroBase R (B.obj j).obj 1 (by omega) 1) =
    (postnikovCommonRightContourBottomRefinedPath R f c d hj).hom ≫
      Path.map R (SquareZero.baseChangeMap
        (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) :=
  PostnikovCommonCore.postnikovCommonRightGammaSourceWitness_zeroClass
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

lemma postnikovCommonRightGammaSourceWitness_nativeClass :
    ((postnikovCommonRightGammaSourceWitness R f c d hj).hom ≫
      Path.map R (postnikovPerturbedClass R (B.obj j).obj 1 (by omega))) ≫
        Path.map R ((postnikovNativeZeroIso R (B.obj j).obj 1 (by omega) 1).hom ≫
          SquareZero.baseChangeMap (postnikovTransition R (B.obj j).obj 1 0 (by omega))
            (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) =
    (postnikovCommonRightContourBottomRefinedPath R f c d hj).hom ≫
      Path.map R (SquareZero.baseChangeMap
        (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) :=
  PostnikovCommonCore.postnikovCommonRightGammaSourceWitness_nativeClass
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
