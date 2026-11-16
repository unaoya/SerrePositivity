module
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceFiberPairingRoof
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.UnderRightOpPairing
public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceNativeFiberPath
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoEndpointProjection

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

def strictBETotJointSourceRawCosliceFamily (A : Type u) [CommRing A] (P : strictBETotJointHomIndex A) :
    let c := modelRelativeObject (operad A).Algebra
      ((rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2)
    let Fop := (nerveOppositeIso (C := (modelRelativeCategory (operad A).Algebra).category)).inv ≫
      SSet.opFunctor.map (strictBETotModelSource A)
    nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P) ⟶
      sliceUnder (nervePoint (Opposite.op c) ≫ Fop) := by
  dsimp only
  let c := modelRelativeObject (operad A).Algebra
    ((rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2)
  let Fop := (nerveOppositeIso (C := (modelRelativeCategory (operad A).Algebra).category)).inv ≫
    SSet.opFunctor.map (strictBETotModelSource A)
  exact nerveMap (Under.lift (X := Opposite.op c)
      (strictBETotJointSourceRoofFrameDiagram A P).rightOp
      (NatTrans.rightOp (strictBETotJointSourceRoofFrameEvaluation A P))) ≫
    nerveUnderMap (Opposite.op c) ≫ sliceUnderPostcomp (nervePoint (Opposite.op c)) Fop
lemma strictBETotJointSourceRawCosliceFamily_pairing (A : Type u) [CommRing A] (P : strictBETotJointHomIndex A) :
    let c := modelRelativeObject (operad A).Algebra
      ((rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2)
    let Fop := (nerveOppositeIso (C := (modelRelativeCategory (operad A).Algebra).category)).inv ≫
      SSet.opFunctor.map (strictBETotModelSource A)
    strictBETotJointSourceRawCosliceFamily A P ≫ cosliceOppositeTwistedArrowMap (nervePoint (Opposite.op c) ≫ Fop) =
      simplicialElementsFiberInclusion (strictBETotJointSourceCoefficients A) P ≫
        strictBETotJointSourceNativePairing A := by
  dsimp only
  have hn := nerveUnderLift_rightOp_native_pairing
    (strictBETotJointSourceRoofFrameEvaluation A P) (strictBETotModelSource A)
  have hp := congrArg (fun f :
      nerve ((simplicialElementsCatDiagram (strictBETotJointSourceCoefficients A)).obj P) ⟶
        TwistedArrow (nerve (modelRelativeCategory (operad A).Algebra).category) =>
      f ≫ edgewiseSubdivisionMap (strictBETotModelSource A)) (strictBETotJointSourceFiberPairing_roof_eq A P)
  have hh := hn.trans hp.symm
  simpa only [strictBETotJointSourceRawCosliceFamily, strictBETotJointSourceNativePairing,
    simplicialElementsFiberInclusion_eq_nerveMap, Category.assoc, id_eq] using hh
def strictBETotJointSourceCorrectedRawCosliceIso (A : Type u) [CommRing A] (P : strictBETotJointHomIndex A) :
    let c := modelRelativeObject (operad A).Algebra
      ((rightFrameReplacement (rightFrameFamily A)).obj (AsSmall.down.obj P).2)
    let Fop := (nerveOppositeIso (C := (modelRelativeCategory (operad A).Algebra).category)).inv ≫
      SSet.opFunctor.map (strictBETotModelSource A)
    FunctorIso
      (simplicialElementsFiberInclusion (strictBETotJointSourceCoefficients A) P ≫
        strictBETotJointSourceCorrectedPairing A)
      (strictBETotJointSourceRawCosliceFamily A P ≫ cosliceOppositeTwistedArrowMap (nervePoint (Opposite.op c) ≫ Fop)) := by
  dsimp only
  exact functorIsoOfEq (strictBETotJointSourceFiberPairingIso A P) rfl
    (strictBETotJointSourceRawCosliceFamily_pairing A P).symm
end SerrePositivity.EInfinity.BarrattEccles
end
