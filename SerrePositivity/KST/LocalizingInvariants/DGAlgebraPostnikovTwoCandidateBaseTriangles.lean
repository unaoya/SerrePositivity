module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoCandidateBaseValue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNonpositiveRoofValue

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorCandidateBaseTriangles

/-!
概要：実二切断候補と元の f の合成を τ₁ へ射影すると、元の両遷移に一致する。
方針：候補の底の式と元の τ₁ 逆 roof の左右三角形を、元の切断自然性で結ぶ。
規約：二切断全体の逆三角形は未主張。使われ方：残る π₂ の作用の検証。
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

lemma candidateRoof_value_left_base :
    (L.map (postnikovMap R (f.app d.layerInverse.zero.stage).hom 2) ≫
      SurjectiveRoof.value R L hL (d.candidateRoof R)) ≫
        L.map (postnikovTransition R (A.obj j).obj 2 1 (by omega)) =
    L.map (postnikovMap R (A.transition (d.target_le.trans
      (d.layerInverse.zero.inverse_le.trans d.layerInverse.zero.stage_le))).hom 2) ≫
        L.map (postnikovTransition R (A.obj j).obj 2 1 (by omega)) :=
  PostnikovSuccessorClassInverseData.candidateRoof_value_left_base
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R) (D := D) (L := L) (hL := hL)

lemma candidateRoof_value_right_base :
    (SurjectiveRoof.value R L hL (d.candidateRoof R) ≫ L.map (postnikovMap R (f.app j).hom 2)) ≫
      L.map (postnikovTransition R (B.obj j).obj 2 1 (by omega)) =
    L.map (postnikovMap R (B.transition (d.target_le.trans
      (d.layerInverse.zero.inverse_le.trans d.layerInverse.zero.stage_le))).hom 2) ≫
        L.map (postnikovTransition R (B.obj j).obj 2 1 (by omega)) :=
  PostnikovSuccessorClassInverseData.candidateRoof_value_right_base
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R) (D := D) (L := L) (hL := hL)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
