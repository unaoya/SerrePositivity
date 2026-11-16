module

public import SerrePositivity.EInfinity.BarrattEccles.StrictDiagramTotJointSourceNativePinched
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans.TwistedHomOppositeIntervalFamilyComparison

/-! 元のnative pinched射そのものの全interval族を、同じ既存比較で正規化する。 -/

@[expose] public section
open CategoryTheory SSet
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
open SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes
open SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TwistedArrowsAndCospans
open SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories
universe u
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

end

noncomputable section
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
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
variable (A : Type u) [CommRing A]
attribute [local instance] jointNativePinchedModel jointNativePinchedFactorization

attribute [local instance] vertexFiber_kanComplex_of_leftFibration


/-- 元のnative射自身の全族を、同じ指定逆によるcosliceの全族へ戻す。 -/
lemma strictBETotJointSourceNativePinchedMap_interval_family_normalization (P : strictBETotJointHomIndex A) :
    let x := (strictBETotModelSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex (((strictBETotJointHomSourceIndex A).obj P).unop))
    let y := (strictBETotModelSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex ((strictBETotJointHomTargetIndex A).obj P))
    let e := SSet.opFunctor.mapIso (eqToIso
      (congrArg (fun b => vertexFiber (twistedArrowProjection (CAlg_R A)) b)
        (strictBETotJointNativeHomInput_model_vertex A P)))
    intervalFamilyHom (strictBETotJointSourceNativePinchedMap A P ≫
      pinchedHomToIntervalMappingSpace x y) =
      intervalFamilyHom (strictBETotJointSourceNativeOppositeFiberMap A P ≫ e.hom ≫
        (isQCatEquivalence_of_trivialKanFibration (edgewiseLeft (twistedArrowHomSpace x y))).choose.inv ≫
        edgewiseRight (twistedArrowHomSpace x y) ≫
        (cosliceTwistedHomMap_isQCatEquivalence x y).choose.inv ≫
        cosliceFiberToIntervalMappingSpace x y) := by
  dsimp only
  exact twistedArrowHomOppositePinchedEquivalence_interval_family_comp
    (x := (strictBETotModelSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex (((strictBETotJointHomSourceIndex A).obj P).unop)))
    (y := (strictBETotModelSource A).app (Opposite.op ⦋0⦌)
      (nerveVertex ((strictBETotJointHomTargetIndex A).obj P)))
    (strictBETotJointSourceNativeOppositeFiberMap A P)
    (SSet.opFunctor.mapIso (eqToIso
      (congrArg (fun b => vertexFiber (twistedArrowProjection (CAlg_R A)) b)
        (strictBETotJointNativeHomInput_model_vertex A P)))).hom
    (strictBETotJointNativeFiberPinchedEquivalence A P).hom rfl

end SerrePositivity.EInfinity.BarrattEccles
end
