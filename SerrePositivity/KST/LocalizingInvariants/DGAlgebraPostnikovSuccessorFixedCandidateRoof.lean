module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedClassMap
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorCandidateRoof

/-!
概要：指定右経路の新 class 互換性を、元の次段切断代数間の実非正次数 roof 候補へ移す。
方針：元の源比較を相対模型へ戻し、新 Γ 射と元の標的比較を実 roof で合成する。
規約：両逆三角形は未主張。使われ方：整合する次段切断の逆候補の検証。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} {hn : 0 ≤ n} {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovSuccessorClassInverseData R hn f j)

def classModelFixedCandidateRoof :
    SurjectiveRoof R (d.sourceModel R) (originalTargetModel (n := n) (hn := hn) (A := A) (j := j) R) :=
  (SurjectiveRoof.ofQuasiIsoInverse R (d.sourceRelativeComparison R)
    (d.sourceRelativeComparison_quasiIso R)).postcompose R
    (d.sourceToTargetFixedRelative R ≫ d.targetRelativeComparison R ≫ d.targetToOriginalModel R)

def rawFixedCandidateRoof : SurjectiveRoof R
    (postnikov R (B.obj d.layerInverse.zero.stage).obj (n + 1)) (postnikov R (A.obj j).obj (n + 1)) :=
  ((d.sourceUpperRoof R).comp R (d.classModelFixedCandidateRoof R)).comp R
    (targetUpperRoof (A := A) (j := j) R)

def fixedCandidateRoof : SurjectiveRoof R
    (postnikov R (B.obj d.layerInverse.zero.stage).obj (n + 1)) (postnikov R (A.obj j).obj (n + 1)) :=
  (d.rawFixedCandidateRoof R).nonpositiveNormalization R

lemma fixedCandidateRoof_nonpositive : (d.fixedCandidateRoof R).apex.X.IsStrictlyLE 0 :=
  (d.rawFixedCandidateRoof R).nonpositiveNormalization_apex R

lemma fixedCandidateRoof_denominator_quasiIso : QuasiIso (d.fixedCandidateRoof R).denominator.hom :=
  (d.fixedCandidateRoof R).denominator_quasiIso

lemma fixedCandidateRoof_denominator_epi : Epi (d.fixedCandidateRoof R).denominator.hom :=
  (d.fixedCandidateRoof R).denominator_epi

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
