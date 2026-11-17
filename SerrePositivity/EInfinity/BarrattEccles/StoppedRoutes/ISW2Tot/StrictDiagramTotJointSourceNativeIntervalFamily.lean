module

public import SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.StrictDiagramTotJointSourceNativePinched
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedHomOppositeIntervalFamilyComparison

/-!
状態：D81により停止したBE模型のIS-W2 Tot経路。既存の到達点の保管用。 元のnative pinched射そのものの全interval族を、同じ既存比較で正規化する。 -/

@[expose] public section
open _root_.CategoryTheory _root_.SSet
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open scoped _root_.Simplicial
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

end

noncomputable section
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
open scoped _root_.Simplicial
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
variable (A : Type u) [CommRing A]
attribute [local instance] _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.jointNativePinchedModel _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.jointNativePinchedFactorization

attribute [local instance] vertexFiber_kanComplex_of_leftFibration


/-- 元のnative射自身の全族を、同じ指定逆によるcosliceの全族へ戻す。 -/
lemma strictBETotJointSourceNativePinchedMap_interval_family_normalization (P : _root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomIndex A) :
    let x := (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomSourceIndex A).obj P).unop))
    let y := (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomTargetIndex A).obj P))
    let e := SSet.opFunctor.mapIso (eqToIso
      (congrArg (fun b => vertexFiber (twistedArrowProjection (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)) b)
        (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomInput_model_vertex A P)))
    intervalFamilyHom (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativePinchedMap A P ≫
      pinchedHomToIntervalMappingSpace x y) =
      intervalFamilyHom (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeOppositeFiberMap A P ≫ e.hom ≫
        (isQCatEquivalence_of_trivialKanFibration (edgewiseLeft (twistedArrowHomSpace x y))).choose.inv ≫
        edgewiseRight (twistedArrowHomSpace x y) ≫
        (cosliceTwistedHomMap_isQCatEquivalence x y).choose.inv ≫
        cosliceFiberToIntervalMappingSpace x y) := by
  dsimp only
  exact twistedArrowHomOppositePinchedEquivalence_interval_family_comp
    (x := (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex (((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomSourceIndex A).obj P).unop)))
    (y := (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotModelSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex ((_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointHomTargetIndex A).obj P)))
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointSourceNativeOppositeFiberMap A P)
    (SSet.opFunctor.mapIso (eqToIso
      (congrArg (fun b => vertexFiber (twistedArrowProjection (_root_.SerrePositivity.EInfinity.BarrattEccles.CAlg_R A)) b)
        (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeHomInput_model_vertex A P)))).hom
    (_root_.SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot.strictBETotJointNativeFiberPinchedEquivalence A P).hom rfl

end SerrePositivity.EInfinity.BarrattEccles.StoppedRoutes.ISW2Tot
end
