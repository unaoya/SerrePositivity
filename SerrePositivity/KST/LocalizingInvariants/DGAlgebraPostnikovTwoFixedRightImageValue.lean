module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRightWModelHomotopy
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightDirectValue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSurjectiveRoofValue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSurjectiveRoofConnectiveValue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConnectiveQuasiIso

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightImageValue

/-!
概要：直接 B 遷移と元の fixed roof の fⱼ 後合成を、同じ不変量値で比較する。
方針：一定底の fⱼ 自然性と動く底の W を順に写し、元の source 係数模型を前合成する。
規約：元の実模型射と roof を保持。使われ方：二切断逆の実右三角形への接続。
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
  {C : Type v} [Category.{w} C] (L : Mon (Complex R) ⥤ C)

lemma rightImage_completed_map_eq (hL : InvertsQuasiIsos R L) :
    L.map (d.rightImageRelativeToOriginalModel R) = L.map (d.rightWCompletedModel R) :=
  PostnikovSuccessorClassInverseData.rightImage_completed_map_eq
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R) (C := C) (L := L) (hL := hL)

lemma rightImage_completed_map_eq_of_connective (hL : InvertsConnectiveQuasiIsos R L) :
    L.map (d.rightImageRelativeToOriginalModel R) = L.map (d.rightWCompletedModel R) :=
  PostnikovSuccessorClassInverseData.rightImage_completed_map_eq_of_connective
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R) (C := C) (L := L) (hL := hL)

lemma sourceToRightCompletedModel_original :
    d.sourceToRightCompletedModel R ≫ d.fixedRightCompletedRelativeToOriginalModel R =
    d.sourceToRightCoefficientModel R ≫ d.rightWCompletedModel R :=
  PostnikovSuccessorClassInverseData.sourceToRightCompletedModel_original
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma directOriginal_rightImage_map_eq (hL : InvertsQuasiIsos R L) :
    L.map (d.directOriginalModelMap R) =
      L.map (d.sourceToRightCoefficientModel R ≫ d.rightImageRelativeToOriginalModel R) :=
  PostnikovSuccessorClassInverseData.directOriginal_rightImage_map_eq
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R) (C := C) (L := L) (hL := hL)

lemma directOriginal_rightImage_map_eq_of_connective (hL : InvertsConnectiveQuasiIsos R L) :
    L.map (d.directOriginalModelMap R) =
      L.map (d.sourceToRightCoefficientModel R ≫ d.rightImageRelativeToOriginalModel R) :=
  PostnikovSuccessorClassInverseData.directOriginal_rightImage_map_eq_of_connective
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R) (C := C) (L := L) (hL := hL)

def classModelRightDirectRoof : SurjectiveRoof R (d.sourceModel R)
    (postnikovClassModel R (B.obj j).obj 1 (by omega)) :=
  PostnikovSuccessorClassInverseData.classModelRightDirectRoof
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma classModelFixedCandidateRoof_post_f_value (hL : InvertsQuasiIsos R L) :
    SurjectiveRoof.value R L hL ((d.classModelFixedCandidateRoof R).postcompose R
      (postnikovClassModelMap R 1 (by omega) (f.app j).hom)) =
    SurjectiveRoof.value R L hL (d.classModelRightDirectRoof R) :=
  PostnikovSuccessorClassInverseData.classModelFixedCandidateRoof_post_f_value
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R) (C := C) (L := L) (hL := hL)

lemma sourceModel_isConnective : IsConnective R (d.sourceModel R) :=
  PostnikovSuccessorClassInverseData.sourceModel_isConnective
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R)

lemma classModelFixedCandidateRoof_post_f_connectiveValue
    (hL : InvertsConnectiveQuasiIsos R L) :
    SurjectiveRoof.connectiveValue R L hL (d.sourceModel_isConnective R)
      ((d.classModelFixedCandidateRoof R).postcompose R
        (postnikovClassModelMap R 1 (by omega) (f.app j).hom)) =
    SurjectiveRoof.connectiveValue R L hL (d.sourceModel_isConnective R)
      (d.classModelRightDirectRoof R) :=
  PostnikovSuccessorClassInverseData.classModelFixedCandidateRoof_post_f_connectiveValue
    (R := R) (n := (1 : ℤ)) (hn := by decide) (A := A) (B := B) (f := f) (j := j)
    (d := d.toSuccessor R) (C := C) (L := L) (hL := hL)

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
