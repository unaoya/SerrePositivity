module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightDirectSourcePath
public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightDenCoefficientRestore
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPathImageWhisker

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightDirectClassRestore

/-!
概要：元の直接 class 模型射の経路を復元すると、元の source 自然性の class 像に一致する。
方針：指定直接経路の全射式と係数復元三角形を、元の Path.map の合成則で繋ぐ。
規約：端点だけでなく全 class 経路を同定。使われ方：模型の source 経路の実適用。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

lemma fixedRightDirectWitness_restore : (d.fixedRightDirectWitness R).hom ≫
    Path.map R (d.rightDenominatorClassRestore R) =
    (d.fixedRightDirectSourcePath R).hom ≫
      Path.map R (postnikovPerturbedClass R (B.obj j).obj 1 (by omega)) :=
  PostnikovSuccessorClassInverseData.fixedRightDirectWitness_restore
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
