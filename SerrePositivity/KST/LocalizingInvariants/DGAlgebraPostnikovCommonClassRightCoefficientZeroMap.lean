module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonClassRightCoefficientTriangle
public import SerrePositivity.KST.LocalizingInvariants.DGSquareZeroUnderlyingMaps

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreClassRightCoefficientZeroMap
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：実 fⱼ 係数射の零 class 像が、元の native class 互換性で使った右射と一致する。
方針：元の P 底射と層射を保つ二座標の公式を比較する。
規約：実代数射全体の等式を保持。使われ方：fixed 模型射の係数表示と native 経路の照合。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {i m : ℕ} {hi : i ≤ m} (c : NonpositiveInverseRoof R (f.map (postnikovFunctor R 1)) i m hi)
  (d : PostnikovCommonLayerInverse R f c) {j : ℕ} (hj : j ≤ i)

lemma postnikovCommonClassRightTargetCoefficient_zero_map :
    SquareZero.coefficientMap (postnikovCommonClassBase R f c d)
      (postnikovCommonClassRightTargetCoefficient R f c d hj) ≫
      SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1) =
    postnikovCommonClassFixedZeroMap R f c d hj :=
  PostnikovCommonCore.postnikovCommonClassRightTargetCoefficient_zero_map
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
