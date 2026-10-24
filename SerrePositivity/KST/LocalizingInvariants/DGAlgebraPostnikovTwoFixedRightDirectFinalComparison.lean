module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightDirectFinalPathComparison

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightDirectFinalComparison

/-!
概要：source 模型経路の終点を、元の直接 class 模型射の元の Bⱼ 模型への合成へ同定する。
方針：二射影と全経路を保つ実模型の一意性を使う。
規約：元の直接 B 遷移の模型合成を始点に保持。使われ方：右逆三角形の直接側。
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

lemma directSourceFinalModelMap_eq_fixed : d.directSourceFinalModelMap R =
    d.fixedRightDirectModelMap R ≫ d.fixedRightCompletedRelativeToOriginalModel R :=
  PostnikovSuccessorClassInverseData.directSourceFinalModelMap_eq_fixed
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def directOriginalToFixedModelHomotopy : Path.Witness R (d.directOriginalModelMap R)
    (d.fixedRightDirectModelMap R ≫ d.fixedRightCompletedRelativeToOriginalModel R) :=
  PostnikovSuccessorClassInverseData.directOriginalToFixedModelHomotopy
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
