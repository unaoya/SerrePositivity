module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonRightDenFirstPath

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreRightSourceFirstComparison
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovCommonCoreSpecialization

/-!
概要：元の S の B 遷移後の持ち上げを、Γ 源上の零底 affine 第一経路そのものに同定する。
方針：元の全零 class 像を第一 ImageWitness の式で照合し、同じ P 射影の一意性を使う。
規約：経路の一致は証明の結論。使われ方：S′・L・W の境界の実比較。
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

lemma postnikovCommonRightSourceFirst_map :
    (postnikovCommonRightSourceRefinedPath R f c d hj).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) =
    (postnikovCommonRightDenFirstZeroPath R f c d hj).hom ≫ Path.map R
      (SquareZero.baseChangeMap (postnikovCommonRightClassifyingBase R f c d hj)
        (DGBimoduleShift.obj (postnikovLayerZeroBimodule R (B.obj j).obj 1) 1)) :=
  PostnikovCommonCore.postnikovCommonRightSourceFirst_map
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

/-- 元の S と affine 第一辺は、同じ Γ 源の全乗法的経路として厳密に一致する。 -/
lemma postnikovCommonRightSourceFirst_hom :
    (postnikovCommonRightSourceRefinedPath R f c d hj).hom =
      (postnikovCommonRightDenFirstZeroPath R f c d hj).hom :=
  PostnikovCommonCore.postnikovCommonRightSourceFirst_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (i := i) (m := m)
    (hi := hi) (c := c) (d := d.toCore R f c) (j := j) (hj := hj)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
