module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoClassModels

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorClassModelMaps

/-!
概要：二切断 class 逆の係数模型射と、標準 class 模型へ向かう実準同型 zigzag を構成。
方針：元の係数射は厳密 cospan 射、class の経路は mapping-path の厳密化に渡す。
規約：四つの射とも元の右脚を保持。使われ方：元の二切断への実 roof 移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)

def sourceToImage : d.sourceModel R ⟶ d.imageModel R :=
  PostnikovSuccessorClassInverseData.sourceToImage
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def imageToPath : d.imageModel R ⟶ d.pathModel R :=
  PostnikovSuccessorClassInverseData.imageToPath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def targetToPath : d.targetComposedModel R ⟶ d.pathModel R :=
  PostnikovSuccessorClassInverseData.targetToPath
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def targetToStandard : d.targetComposedModel R ⟶ d.targetModel R :=
  PostnikovSuccessorClassInverseData.targetToStandard
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma imageToPath_quasiIso : QuasiIso (d.imageToPath R).hom :=
  PostnikovSuccessorClassInverseData.imageToPath_quasiIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma targetToPath_quasiIso : QuasiIso (d.targetToPath R).hom :=
  PostnikovSuccessorClassInverseData.targetToPath_quasiIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma targetToStandard_quasiIso : QuasiIso (d.targetToStandard R).hom :=
  PostnikovSuccessorClassInverseData.targetToStandard_quasiIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma sourceToImage_right : d.sourceToImage R ≫ HomotopyPullbackModel.right R _ _ =
    HomotopyPullbackModel.right R _ _ :=
  PostnikovSuccessorClassInverseData.sourceToImage_right
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma sourceToImage_left : d.sourceToImage R ≫ HomotopyPullbackModel.left R _ _ =
    HomotopyPullbackModel.left R _ _ :=
  PostnikovSuccessorClassInverseData.sourceToImage_left
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma imageToPath_right : d.imageToPath R ≫ HomotopyPullbackModel.right R _ _ =
    HomotopyPullbackModel.right R _ _ :=
  PostnikovSuccessorClassInverseData.imageToPath_right
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma targetToPath_right : d.targetToPath R ≫ HomotopyPullbackModel.right R _ _ =
    HomotopyPullbackModel.right R _ _ :=
  PostnikovSuccessorClassInverseData.targetToPath_right
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma targetToStandard_right : d.targetToStandard R ≫ HomotopyPullbackModel.right R _ _ =
    HomotopyPullbackModel.right R _ _ :=
  PostnikovSuccessorClassInverseData.targetToStandard_right
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
