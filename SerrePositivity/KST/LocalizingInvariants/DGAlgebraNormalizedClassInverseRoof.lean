module

public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraCospanProRoof
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraNormalizedClassPro
public import SerrePositivity.KST.LocalizingInvariants.DGAlgebraPostnikovClassConnective

/-!
概要：元の一切断の class 模型の逆を、実 dg 代数 roof と元の pro 三角形で供給する。
方針：元の π₁ の pro 同型から class 図式の中心の逆を作り、元の cospan の逆を抽出。
規約：同じ実 span を全ての反転関手で評価する。使われ方：元の一切断射の逆の抽出。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
open CategoryTheory
open SerrePositivity.DifferentialGraded
namespace SerrePositivity.KST.LocalizingInvariants.DGAlgebra
open ProExcision
variable (R : Type u) [CommRing R] {A B : Tower (NonpositiveAlgebra R)} (f : LevelHom A B)
  {D : Type v} [Category.{w} D]

lemma postnikovNormalizedClass_hasRoofProInverse
    (hf : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1))) :
    HasSurjectiveRoofProInverse R (D := D)
      ((postnikovStrictZeroBaseNonpositiveLift R f 1 (by omega)).map
        (postnikovClassModelFunctor R 0 (by omega))) := by
  apply HomotopyPullbackModel.hasSurjectiveRoofProInverse R
    ((postnikovStrictZeroBaseNonpositiveLift R f 1 (by omega)).map
      (postnikovClassCospanFunctor R 0 (by omega)))
  · exact postnikovNormalizedPerturbedMap_quasiIso R f
  · exact postnikovNormalizedDerivationTargetMap_isProIso R f hf
  · change IsProIso ((postnikovStrictZeroBaseNonpositiveLift R f 1 (by omega)).map
      (postnikovFunctor R 0))
    have : ∀ i, IsIso (((postnikovStrictZeroBaseNonpositiveLift R f 1 (by omega)).map
        (postnikovFunctor R 0)).app i) :=
      postnikovStrictZeroBaseLift_zeroMap_isIso R f 1 (by omega)
    exact TowerDiagram.isProIso_of_levelwiseIso _

lemma postnikovNormalizedClass_hasConnectiveRoofProInverse
    (hf : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1))) :
    HasConnectiveRoofProInverse R (D := D)
      ((postnikovStrictZeroBaseNonpositiveLift R f 1 (by omega)).map
        (postnikovClassModelFunctor R 0 (by omega)))
      (fun i => postnikovClassModel_isConnective R
        ((postnikovStrictZeroBaseNonpositiveTower R f 1 (by omega)).obj i).obj 0 (by omega)) := by
  apply HomotopyPullbackModel.hasConnectiveRoofProInverse R
    ((postnikovStrictZeroBaseNonpositiveLift R f 1 (by omega)).map
      (postnikovClassCospanFunctor R 0 (by omega)))
  · exact postnikovNormalizedPerturbedMap_quasiIso R f
  · exact postnikovNormalizedDerivationTargetMap_isProIso R f hf
  · change IsProIso ((postnikovStrictZeroBaseNonpositiveLift R f 1 (by omega)).map
      (postnikovFunctor R 0))
    have : ∀ i, IsIso (((postnikovStrictZeroBaseNonpositiveLift R f 1 (by omega)).map
        (postnikovFunctor R 0)).app i) :=
      postnikovStrictZeroBaseLift_zeroMap_isIso R f 1 (by omega)
    exact TowerDiagram.isProIso_of_levelwiseIso _

lemma postnikovNormalizedClass_hasNativeRoofProInverse
    (hf : IsProIso ((f.map (nonpositiveInclusion R)).map (groups R 1))) :
    HasNativeRoofProInverse R
      ((postnikovStrictZeroBaseNonpositiveLift R f 1 (by omega)).map
        (postnikovClassModelFunctor R 0 (by omega))) := by
  apply HomotopyPullbackModel.hasNativeRoofProInverse R
    ((postnikovStrictZeroBaseNonpositiveLift R f 1 (by omega)).map
      (postnikovClassCospanFunctor R 0 (by omega)))
  · exact postnikovNormalizedPerturbedMap_quasiIso R f
  · exact postnikovNormalizedDerivationTargetMap_isProIso R f hf
  · change IsProIso ((postnikovStrictZeroBaseNonpositiveLift R f 1 (by omega)).map
      (postnikovFunctor R 0))
    have : ∀ i, IsIso (((postnikovStrictZeroBaseNonpositiveLift R f 1 (by omega)).map
        (postnikovFunctor R 0)).app i) :=
      postnikovStrictZeroBaseLift_zeroMap_isIso R f 1 (by omega)
    exact TowerDiagram.isProIso_of_levelwiseIso _

end SerrePositivity.KST.LocalizingInvariants.DGAlgebra
