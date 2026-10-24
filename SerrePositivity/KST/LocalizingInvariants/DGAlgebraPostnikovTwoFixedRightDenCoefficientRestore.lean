module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightDenRestore

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightDenCoefficientRestore

/-!
概要：元の直接分母係数模型射を、元の B 遷移の class 標的射へ戻す。
方針：元の双加群射の全射式と係数同型の恒等 underlying 射を使う。
規約：H⁻² だけでなく実係数射の三角形。使われ方：直接模型射の元の分母比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

lemma rightDenominatorCoefficientIso_hom : (d.rightDenominatorCoefficientIso R).hom.hom =
    𝟙 ((postnikovLayer R (B.obj j).obj 1)⟦(1 : ℤ)⟧) :=
  PostnikovSuccessorClassInverseData.rightDenominatorCoefficientIso_hom
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightDenominatorCoefficient_factor : d.rightDenominatorCoefficient R =
    postnikovCellClassOverCoefficient R (B.obj d.layerInverse.zero.stage).obj (B.obj j).obj
      (d.classBase R) 1 (by omega) (d.lowerBaseInverse R).roof.denominator
      (postnikovCommonRightDenDirectMap R f d.baseInverse d.layerInverse d.target_le) ≫
        (d.rightDenominatorCoefficientIso R).hom :=
  PostnikovSuccessorClassInverseData.rightDenominatorCoefficient_factor
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma rightDenominatorCoefficient_restore :
    SquareZero.coefficientMap (d.classBase R) (d.rightDenominatorCoefficient R) ≫
      d.rightDenominatorClassRestore R =
    SquareZero.baseChangeMap (d.lowerBaseInverse R).roof.denominator
      (postnikovShiftedLayerBimodule R (B.obj d.layerInverse.zero.stage).obj 1 (by omega) 1) ≫
      postnikovDerivationTargetMap R
        (postnikovCommonRightDenDirectMap R f d.baseInverse d.layerInverse d.target_le)
        1 (by omega) :=
  PostnikovSuccessorClassInverseData.rightDenominatorCoefficient_restore
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
