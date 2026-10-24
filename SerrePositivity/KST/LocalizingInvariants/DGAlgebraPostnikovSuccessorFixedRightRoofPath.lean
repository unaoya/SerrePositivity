module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovSuccessorFixedRightCellPath
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraQuasiIsoInverseRoofRightPath

/-!
概要：元の fixed class roof を有限 cell 細分し、fⱼ 後合成の実右三角形を構成する。
方針：源準同型比較の実逆 roof と、指定した四模型経路の cell 合成を使う。
規約：元の source 比較の逆 roof を保持。使われ方：上下段比較へ戻す右三角形。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
open ProExcision
variable (R : Type u) [CommRing R] {n : ℤ} {hn : 0 ≤ n} {A B : Tower (NonpositiveAlgebra R)} {f : LevelHom A B}
  {j : ℕ} (d : PostnikovSuccessorClassInverseData R hn f j)

abbrev classModelFixedRightRoof := (d.classModelFixedCandidateRoof R).cellRefinement R 2

def classModelFixedRightRoofPath : Path.Witness R
    ((d.classModelFixedRightRoof R).numerator ≫
      postnikovClassModelMap R n hn (f.app j).hom)
    ((d.classModelFixedRightRoof R).denominator ≫
      (d.sourceToOriginalModel R ≫ postnikovClassModelMap R n hn
        (PostnikovCommonCore.postnikovCommonRightDenDirectMap R hn f d.baseInverse d.layerInverse d.target_le))) :=
  SurjectiveRoof.inversePostcomposeRightPath R (d.sourceRelativeComparison R)
    (d.sourceRelativeComparison_quasiIso R) (d.fixedTargetModelMap R)
    (postnikovClassModelMap R n hn (f.app j).hom)
    (d.sourceToOriginalModel R ≫ postnikovClassModelMap R n hn
      (PostnikovCommonCore.postnikovCommonRightDenDirectMap R hn f d.baseInverse d.layerInverse d.target_le)) 3
    (d.fixedRightClassModelPath R)

variable {D : Type v} [Category.{w} D] (L : Mon (Complex R) ⥤ D)

lemma classModelFixedRightRoof_value (hL : InvertsQuasiIsos R L) :
    SurjectiveRoof.value R L hL (d.classModelFixedRightRoof R) =
      SurjectiveRoof.value R L hL (d.classModelFixedCandidateRoof R) :=
  SurjectiveRoof.cellRefinement_value R _ L hL 2

lemma classModelFixedRightRoof_connectiveValue (hL : InvertsConnectiveQuasiIsos R L) :
    SurjectiveRoof.connectiveValue R L hL (d.sourceModel_isConnective R)
      (d.classModelFixedRightRoof R) =
    SurjectiveRoof.connectiveValue R L hL (d.sourceModel_isConnective R)
      (d.classModelFixedCandidateRoof R) :=
  SurjectiveRoof.cellRefinement_connectiveValue R _ L hL (d.sourceModel_isConnective R) 2

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra.PostnikovSuccessorClassInverseData
