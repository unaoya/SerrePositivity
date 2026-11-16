module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceRawCosliceFamily

/-!
概要：元のfiberの全pairingを同じsource-frame評価の表示へ照合する。
方針：同じ添字の関手と評価を比較し、指定済みの全同型と底のpathを保持する。
規約：元のfiber・射・指定pathを変更せず、同値性はまだ主張しない。
使われ方：native fiberと元のroof比較を全関手上で照合する。
-/
open CategoryTheory
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.BarrattEccles
open CategoryTheory HomotopicalAlgebra SSet Limits
open SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open scoped Simplicial
attribute [local instance] jointFiberElementsModel jointFiberElementsFactorization

lemma strictBETotJointSourceCorrectedRawCosliceIso_postcomp (A : Type u) [CommRing A] (P : strictBETotJointHomIndex A) :
    HEq ((functorIsoOfEq (strictBETotJointSourceFiberPairingIso A P) rfl
      (strictBETotJointSourceRawCosliceFamily_pairing A P).symm).postcomp (twistedArrowProjection (CAlg_R A)))
      ((strictBETotJointSourceFiberPairingIso A P).postcomp (twistedArrowProjection (CAlg_R A))) := by
  exact SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.functorIsoOfEq_postcomp_heq
    (strictBETotJointSourceFiberPairingIso A P) rfl (strictBETotJointSourceRawCosliceFamily_pairing A P).symm
    (twistedArrowProjection (CAlg_R A))
lemma strictBETotJointSourceCorrectedRawCosliceIso_original_path (A : Type u) [CommRing A]
    (P : strictBETotJointHomIndex A) :
    HEq ((functorIsoOfEq (strictBETotJointSourceFiberPairingIso A P) rfl
      (strictBETotJointSourceRawCosliceFamily_pairing A P).symm).postcomp (twistedArrowProjection (CAlg_R A)))
      (FunctorIso.precomp (eqToIso (congrArg (fun v => HomotopyCategory.mk (functorVertex v))
        (strictBETotJointSourceCorrectedPairing_projection A)) ≪≫
          strictBETotJointSourcePairingBasePathIso A)
            (simplicialElementsFiberInclusion (strictBETotJointSourceCoefficients A) P)) :=
  (strictBETotJointSourceCorrectedRawCosliceIso_postcomp A P).trans
    (heq_of_eq (strictBETotJointSourceFiberPairingIso_postcomp A P))
end SerrePositivity.EInfinity.BarrattEccles
end
