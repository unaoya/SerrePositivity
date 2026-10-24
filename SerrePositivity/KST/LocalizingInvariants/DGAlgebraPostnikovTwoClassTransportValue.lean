module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoClassTransportIso
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraQuasiIsoInverseRoofNaturality

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorClassTransportValue

/-!
概要：相対 class 同型から戻した実 roof の値は、元の絶対模型の両脚を保つ。
方針：実同型の両脚の式と、準同型逆 roof の元の脚の自然性を合成する。
規約：全準同型を反転する関手を入力。使われ方：元の候補 roof の class 経路の補正。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovTwoClassInverseData R f j)
  {D : Type v} [Category.{w} D] (L : Mon (Complex R) ⥤ D) (hL : InvertsQuasiIsos R L)

lemma classRelativePathRoof_value_left :
    SurjectiveRoof.value R L hL (d.classRelativePathRoof R) ≫
      L.map (HomotopyPullbackModel.left R (d.targetClass R) _) =
        L.map (HomotopyPullbackModel.left R (d.imageClass R) _) :=
  PostnikovSuccessorClassInverseData.classRelativePathRoof_value_left
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R) (D := D) (L := L) (hL := hL)

lemma classRelativePathRoof_value_right :
    SurjectiveRoof.value R L hL (d.classRelativePathRoof R) ≫
      L.map (HomotopyPullbackModel.right R (d.targetClass R) _) =
        L.map (HomotopyPullbackModel.right R (d.imageClass R) _) :=
  PostnikovSuccessorClassInverseData.classRelativePathRoof_value_right
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R) (D := D) (L := L) (hL := hL)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
