module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoClassTargetModel
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraQuasiIsoInverseRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNonpositiveRoof

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorCandidateRoof

/-!
概要：元の class 整合データから、元の二切断代数間の実非正次数 roof 候補を構成する。
方針：係数模型射と準同型 zigzag を実 roof で合成し、元の二切断比較の両端へ戻す。
規約：元の f との逆三角形は未主張。使われ方：二切断の実逆の検証。
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

def classModelCandidateRoof :
    SurjectiveRoof R (d.sourceModel R) (originalTargetModel (A := A) (j := j) R) :=
  PostnikovSuccessorClassInverseData.classModelCandidateRoof
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def sourceUpperRoof : SurjectiveRoof R (postnikov R (B.obj d.layerInverse.zero.stage).obj 2)
    (d.sourceModel R) :=
  PostnikovSuccessorClassInverseData.sourceUpperRoof
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

def targetUpperRoof :
    SurjectiveRoof R (originalTargetModel (A := A) (j := j) R) (postnikov R (A.obj j).obj 2) :=
  PostnikovSuccessorClassInverseData.targetUpperRoof
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (j := j)

def rawCandidateRoof : SurjectiveRoof R (postnikov R (B.obj d.layerInverse.zero.stage).obj 2)
    (postnikov R (A.obj j).obj 2) :=
  PostnikovSuccessorClassInverseData.rawCandidateRoof
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

/-- 元の二切断代数を両端とし、非正次数の実頂点を持つ候補。 -/
def candidateRoof : SurjectiveRoof R (postnikov R (B.obj d.layerInverse.zero.stage).obj 2)
    (postnikov R (A.obj j).obj 2) :=
  PostnikovSuccessorClassInverseData.candidateRoof
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma candidateRoof_nonpositive : (d.candidateRoof R).apex.X.IsStrictlyLE 0 :=
  PostnikovSuccessorClassInverseData.candidateRoof_nonpositive
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma candidateRoof_denominator_quasiIso : QuasiIso (d.candidateRoof R).denominator.hom :=
  PostnikovSuccessorClassInverseData.candidateRoof_denominator_quasiIso
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma candidateRoof_denominator_epi : Epi (d.candidateRoof R).denominator.hom :=
  PostnikovSuccessorClassInverseData.candidateRoof_denominator_epi
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
