module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoRightWModelHomotopy
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovTwoFixedRightDirectValue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSurjectiveRoofValue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraSurjectiveRoofConnectiveValue
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraConnectiveQuasiIso

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
  (Path.Witness.map_eq R L hL (d.rightImageOriginalSourceModelHomotopy R)).trans
    (Path.Witness.map_eq R L hL (d.rightWModelHomotopy R))

lemma rightImage_completed_map_eq_of_connective (hL : InvertsConnectiveQuasiIsos R L) :
    L.map (d.rightImageRelativeToOriginalModel R) = L.map (d.rightWCompletedModel R) := by
  let hB := postnikovClassModel_isConnective R (B.obj j).obj 1 (by omega)
  exact (Path.Witness.map_eq_of_connective R L hL hB
    (d.rightImageOriginalSourceModelHomotopy R)).trans
    (Path.Witness.map_eq_of_connective R L hL hB (d.rightWModelHomotopy R))

lemma sourceToRightCompletedModel_original :
    d.sourceToRightCompletedModel R ≫ d.fixedRightCompletedRelativeToOriginalModel R =
    d.sourceToRightCoefficientModel R ≫ d.rightWCompletedModel R := Category.assoc _ _ _

lemma directOriginal_rightImage_map_eq (hL : InvertsQuasiIsos R L) :
    L.map (d.directOriginalModelMap R) =
      L.map (d.sourceToRightCoefficientModel R ≫ d.rightImageRelativeToOriginalModel R) := by
  have hd := d.directOriginal_completed_map_eq R L hL
  have hi := d.rightImage_completed_map_eq R L hL
  have hm := congrArg (fun t => L.map (d.sourceToRightCoefficientModel R) ≫ t) hi.symm
  exact hd.trans ((congrArg L.map (d.sourceToRightCompletedModel_original R)).trans
    ((L.map_comp _ _).trans (hm.trans (L.map_comp _ _).symm)))

lemma directOriginal_rightImage_map_eq_of_connective (hL : InvertsConnectiveQuasiIsos R L) :
    L.map (d.directOriginalModelMap R) =
      L.map (d.sourceToRightCoefficientModel R ≫ d.rightImageRelativeToOriginalModel R) := by
  have hd := d.directOriginal_completed_map_eq_of_connective R L hL
  have hi := d.rightImage_completed_map_eq_of_connective R L hL
  have hm := congrArg (fun t => L.map (d.sourceToRightCoefficientModel R) ≫ t) hi.symm
  exact hd.trans ((congrArg L.map (d.sourceToRightCompletedModel_original R)).trans
    ((L.map_comp _ _).trans (hm.trans (L.map_comp _ _).symm)))

def classModelRightDirectRoof : SurjectiveRoof R (d.sourceModel R)
    (postnikovClassModel R (B.obj j).obj 1 (by omega)) :=
  (SurjectiveRoof.ofQuasiIsoInverse R (d.sourceRelativeComparison R)
    (d.sourceRelativeComparison_quasiIso R)).postcompose R (d.directOriginalModelMap R)

lemma classModelFixedCandidateRoof_post_f_value (hL : InvertsQuasiIsos R L) :
    SurjectiveRoof.value R L hL ((d.classModelFixedCandidateRoof R).postcompose R
      (postnikovClassModelMap R 1 (by omega) (f.app j).hom)) =
    SurjectiveRoof.value R L hL (d.classModelRightDirectRoof R) := by
  rw [d.classModelFixedCandidateRoof_post_f R]
  change SurjectiveRoof.value R L hL (SurjectiveRoof.postcompose R _ _) =
    SurjectiveRoof.value R L hL (SurjectiveRoof.postcompose R _ _)
  rw [SurjectiveRoof.postcompose_value, SurjectiveRoof.postcompose_value,
    d.directOriginal_rightImage_map_eq R L hL]

lemma sourceModel_isConnective : IsConnective R (d.sourceModel R) :=
  (quasiIso_isConnective_iff R (d.sourceToOriginalModel R)
    (d.sourceToOriginalModel_quasiIso R)).2
      (postnikovClassModel_isConnective R (B.obj d.layerInverse.zero.stage).obj 1 (by omega))

lemma classModelFixedCandidateRoof_post_f_connectiveValue
    (hL : InvertsConnectiveQuasiIsos R L) :
    SurjectiveRoof.connectiveValue R L hL (d.sourceModel_isConnective R)
      ((d.classModelFixedCandidateRoof R).postcompose R
        (postnikovClassModelMap R 1 (by omega) (f.app j).hom)) =
    SurjectiveRoof.connectiveValue R L hL (d.sourceModel_isConnective R)
      (d.classModelRightDirectRoof R) := by
  rw [d.classModelFixedCandidateRoof_post_f R]
  change SurjectiveRoof.connectiveValue R L hL _ (SurjectiveRoof.postcompose R _ _) =
    SurjectiveRoof.connectiveValue R L hL _ (SurjectiveRoof.postcompose R _ _)
  rw [SurjectiveRoof.postcompose_connectiveValue, SurjectiveRoof.postcompose_connectiveValue,
    d.directOriginal_rightImage_map_eq_of_connective R L hL]

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovTwoClassInverseData
