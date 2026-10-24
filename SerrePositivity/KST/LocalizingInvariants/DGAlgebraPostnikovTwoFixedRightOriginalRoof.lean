module

public import
  SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightOriginalTriangle
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedCandidateRoof

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightOriginalRoof

/-!
概要：元の fixed class roof の fⱼ 後合成を、元の係数像模型を通る同じ roof に表示する。
方針：構成済み実模型三角形を、元の源比較の準同型逆 roof の分子へ前合成する。
規約：元の roof の頂点と分母を変更しない。使われ方：実二切断右逆の比較。
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

def classModelRightImageRoof : SurjectiveRoof R (d.sourceModel R)
    (postnikovClassModel R (B.obj j).obj 1 (by omega)) :=
  PostnikovSuccessorClassInverseData.classModelRightImageRoof
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma classModelFixedCandidateRoof_post_f :
    (d.classModelFixedCandidateRoof R).postcompose R
      (postnikovClassModelMap R 1 (by omega) (f.app j).hom) = d.classModelRightImageRoof R :=
  PostnikovSuccessorClassInverseData.classModelFixedCandidateRoof_post_f
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
