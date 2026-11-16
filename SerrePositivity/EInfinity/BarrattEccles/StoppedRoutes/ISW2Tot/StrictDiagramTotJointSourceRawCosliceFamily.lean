module
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointSourceFiberPairingRoof
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.UnderRightOpPairing
public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointSourceNativeFiberPath
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.FunctorIsoEndpointProjection

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。
概要：元のfiberの全pairingを同じsource-frame評価の表示へ照合する。
方針：同じ添字の関手と評価を比較し、指定済みの全同型と底のpathを保持する。
規約：元のfiber・射・指定pathを変更せず、同値性はまだ主張しない。
使われ方：native fiberと元のroof比較を全関手上で照合する。
-/
open _root_.CategoryTheory
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
@[expose] public noncomputable section
namespace SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
open _root_.CategoryTheory _root_.HomotopicalAlgebra _root_.SSet _root_.CategoryTheory.Limits
open _root_.SerrePositivity.InfinityCategories.Project.ModelCategoryComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
open scoped _root_.Simplicial
attribute [local instance] _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.jointFiberElementsModel _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.jointFiberElementsFactorization

def strictBETotJointSourceRawCosliceFamily (A : Type u) [CommRing A] (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    let c := modelRelativeObject (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra
      ((rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)).obj (AsSmall.down.obj P).2)
    let Fop := (nerveOppositeIso (C := (modelRelativeCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).category)).inv ≫
      SSet.opFunctor.map (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A)
    nerve ((simplicialElementsCatDiagram (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)).obj P) ⟶
      sliceUnder (nervePoint (Opposite.op c) ≫ Fop) := by
  dsimp only
  let c := modelRelativeObject (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra
    ((rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)).obj (AsSmall.down.obj P).2)
  let Fop := (nerveOppositeIso (C := (modelRelativeCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).category)).inv ≫
    SSet.opFunctor.map (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A)
  exact nerveMap (Under.lift (X := Opposite.op c)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFrameDiagram A P).rightOp
      (NatTrans.rightOp (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFrameEvaluation A P))) ≫
    nerveUnderMap (Opposite.op c) ≫ sliceUnderPostcomp (nervePoint (Opposite.op c)) Fop
lemma strictBETotJointSourceRawCosliceFamily_pairing (A : Type u) [CommRing A] (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    let c := modelRelativeObject (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra
      ((rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)).obj (AsSmall.down.obj P).2)
    let Fop := (nerveOppositeIso (C := (modelRelativeCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).category)).inv ≫
      SSet.opFunctor.map (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A)
    _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRawCosliceFamily A P ≫ cosliceOppositeTwistedArrowMap (nervePoint (Opposite.op c) ≫ Fop) =
      simplicialElementsFiberInclusion (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A) P ≫
        _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativePairing A := by
  dsimp only
  have hn := nerveUnderLift_rightOp_native_pairing
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRoofFrameEvaluation A P) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A)
  have hp := congrArg (fun f :
      nerve ((simplicialElementsCatDiagram (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A)).obj P) ⟶
        TwistedArrow (nerve (modelRelativeCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).category) =>
      f ≫ edgewiseSubdivisionMap (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A)) (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFiberPairing_roof_eq A P)
  have hh := hn.trans hp.symm
  simpa only [_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRawCosliceFamily, _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativePairing,
    simplicialElementsFiberInclusion_eq_nerveMap, Category.assoc, id_eq] using hh
def strictBETotJointSourceCorrectedRawCosliceIso (A : Type u) [CommRing A] (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    let c := modelRelativeObject (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra
      ((rightFrameReplacement (_root_.SerrePositivity.EInfinity.BarrattEccles.rightFrameFamily A)).obj (AsSmall.down.obj P).2)
    let Fop := (nerveOppositeIso (C := (modelRelativeCategory (_root_.SerrePositivity.EInfinity.BarrattEccles.operad A).Algebra).category)).inv ≫
      SSet.opFunctor.map (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A)
    FunctorIso
      (simplicialElementsFiberInclusion (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCoefficients A) P ≫
        _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceCorrectedPairing A)
      (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRawCosliceFamily A P ≫ cosliceOppositeTwistedArrowMap (nervePoint (Opposite.op c) ≫ Fop)) := by
  dsimp only
  exact functorIsoOfEq (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceFiberPairingIso A P) rfl
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceRawCosliceFamily_pairing A P).symm
end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
end
