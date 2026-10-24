module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightDirectSourceModel

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightDirectInitialComparison

/-!
概要：source 模型経路の始点を、元の source 比較と直接 B 遷移の実模型合成へ同定する。
方針：元の左脚・右脚・全経路を係数復元三角形で同時に比較する。
規約：元の実模型合成を始点に保持。使われ方：直接遷移と fixed 候補の右三角形。
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

def directOriginalModelMap :=
  PostnikovSuccessorClassInverseData.directOriginalModelMap
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma directSourceInitialModelMap_eq_original : d.directSourceInitialModelMap R =
    d.directOriginalModelMap R :=
  PostnikovSuccessorClassInverseData.directSourceInitialModelMap_eq_original
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def directOriginalSourceModelHomotopy : Path.Witness R (d.directOriginalModelMap R)
    (d.directSourceFinalModelMap R) :=
  PostnikovSuccessorClassInverseData.directOriginalSourceModelHomotopy
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
