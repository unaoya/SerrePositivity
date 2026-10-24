module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoClassModelValue

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorCandidateBaseValue

/-!
概要：実二切断候補の底への作用を、元の実一切断逆 roof の値に同定する。
方針：両端の準同型逆 roof の脚の自然性と、class 模型射の元の右脚を組み合わせる。
規約：全準同型反転関手に対する式。二切断全体の逆三角形とは区別する。
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

lemma sourceUpperRoof_value_base_comp :
    SurjectiveRoof.value R L hL (d.sourceUpperRoof R) ≫
      L.map (HomotopyPullbackModel.right R (d.sourceClass R) _ ≫
        (d.lowerBaseInverse R).roof.denominator) =
      L.map (postnikovTransition R (B.obj d.layerInverse.zero.stage).obj 2 1 (by omega)) :=
  PostnikovSuccessorClassInverseData.sourceUpperRoof_value_base_comp
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R) (D := D) (L := L) (hL := hL)

lemma sourceUpperRoof_value_base :
    SurjectiveRoof.value R L hL (d.sourceUpperRoof R) ≫
      L.map (HomotopyPullbackModel.right R (d.sourceClass R) _) =
    L.map (postnikovTransition R (B.obj d.layerInverse.zero.stage).obj 2 1 (by omega)) ≫
      SurjectiveRoof.value R L hL (SurjectiveRoof.ofQuasiIsoInverse R
        (d.lowerBaseInverse R).roof.denominator (d.lowerBaseInverse R).roof.denominator_quasiIso) :=
  PostnikovSuccessorClassInverseData.sourceUpperRoof_value_base
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R) (D := D) (L := L) (hL := hL)

lemma targetUpperRoof_value_base :
    SurjectiveRoof.value R L hL (targetUpperRoof (A := A) (j := j) R) ≫
      L.map (postnikovTransition R (A.obj j).obj 2 1 (by omega)) =
    L.map (HomotopyPullbackModel.right R
      (postnikovPerturbedClass R (A.obj j).obj 1 (by omega)) _) :=
  PostnikovSuccessorClassInverseData.targetUpperRoof_value_base
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (j := j) (D := D) (L := L) (hL := hL)

/-- 元の実候補 roof の τ₁ への射影は、同じ底の実逆 roof の値と可換。 -/
lemma candidateRoof_value_base : SurjectiveRoof.value R L hL (d.candidateRoof R) ≫
    L.map (postnikovTransition R (A.obj j).obj 2 1 (by omega)) =
      L.map (postnikovTransition R (B.obj d.layerInverse.zero.stage).obj 2 1 (by omega)) ≫
        SurjectiveRoof.value R L hL (d.lowerBaseInverse R).roof :=
  PostnikovSuccessorClassInverseData.candidateRoof_value_base
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R) (D := D) (L := L) (hL := hL)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
