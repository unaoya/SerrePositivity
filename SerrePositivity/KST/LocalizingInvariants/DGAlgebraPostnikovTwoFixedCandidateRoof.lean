module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedClassMap
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoCandidateRoof

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedCandidateRoof

/-!
概要：指定右経路の新 class 互換性を、元の二切断代数間の実非正次数 roof 候補へ移す。
方針：元の源比較を相対模型へ戻し、新 Γ 射と元の標的比較を実 roof で合成する。
規約：両逆三角形は未主張。使われ方：整合する二切断の逆候補の検証。
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

def classModelFixedCandidateRoof :
    SurjectiveRoof R (d.sourceModel R) (originalTargetModel (A := A) (j := j) R) :=
  PostnikovSuccessorClassInverseData.classModelFixedCandidateRoof
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def rawFixedCandidateRoof : SurjectiveRoof R
    (postnikov R (B.obj d.layerInverse.zero.stage).obj 2) (postnikov R (A.obj j).obj 2) :=
  PostnikovSuccessorClassInverseData.rawFixedCandidateRoof
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def fixedCandidateRoof : SurjectiveRoof R
    (postnikov R (B.obj d.layerInverse.zero.stage).obj 2) (postnikov R (A.obj j).obj 2) :=
  PostnikovSuccessorClassInverseData.fixedCandidateRoof
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma fixedCandidateRoof_nonpositive : (d.fixedCandidateRoof R).apex.X.IsStrictlyLE 0 :=
  PostnikovSuccessorClassInverseData.fixedCandidateRoof_nonpositive
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma fixedCandidateRoof_denominator_quasiIso : QuasiIso (d.fixedCandidateRoof R).denominator.hom :=
  PostnikovSuccessorClassInverseData.fixedCandidateRoof_denominator_quasiIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma fixedCandidateRoof_denominator_epi : Epi (d.fixedCandidateRoof R).denominator.hom :=
  PostnikovSuccessorClassInverseData.fixedCandidateRoof_denominator_epi
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
