module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoCandidateRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraQuasiIsoInverseRoofNaturality

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorClassModelValue

/-!
概要：実二切断候補の class 模型での評価が、元の共通底への右脚を保つことを示す。
方針：四つの実模型射の右脚の式と、準同型逆 roof の脚の自然性を使う。
規約：ここは全準同型反転関手の界面。具体的不変量への移送は別工程。
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

lemma classModelCandidateRoof_value_right :
    SurjectiveRoof.value R L hL (d.classModelCandidateRoof R) ≫
      L.map (HomotopyPullbackModel.right R
        (postnikovPerturbedClass R (A.obj j).obj 1 (by omega)) _) =
    L.map (HomotopyPullbackModel.right R (d.sourceClass R) _) ≫ L.map (d.targetBase R) :=
  PostnikovSuccessorClassInverseData.classModelCandidateRoof_value_right
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R) (D := D) (L := L) (hL := hL)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
