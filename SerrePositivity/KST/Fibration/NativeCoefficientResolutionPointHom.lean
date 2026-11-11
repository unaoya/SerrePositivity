module
public import SerrePositivity.KST.Fibration.ScaffoldWeightedResolutionPoint

/-! # 元の native 係数点の射を、同じ分類成分と値の表示変更で左解像点へ送る -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 同じ fiber 点の端点表示を等号で変えても、点の射の合成式を保つ。 -/
theorem pointedFiberPointHom_endpointTransport
    {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌} (h : a = b)
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection a) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom v ≫ (eqToIso (congrArg HomotopyCategory.mk h)).hom =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.vertexFiberPointReindex _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceProjection h v) := by
  subst b
  change _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom v ≫ 𝟙 _ = _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom v
  exact Category.comp_id _

/-- 元の native 係数点の射は、同じ指定成分で元の左解像点の射へ移る。 -/
theorem ScaffoldTransportComparisonSpan.nativeCoefficientPointHom_resolution
    {I : Type u} [Category.{u} I] {E : SSet.{u}} {p : E ⟶ nerve I} [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration p]
    (s : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.ScaffoldTransportComparisonSpan p) (c : I) (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransport p c) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom ((nativeTransportPointedFiberMap p (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)).app
      (Opposite.op ⦋0⦌)
        (ULift.up ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportEvaluate p c).app (Opposite.op ⦋0⦌) v))) ≫
      _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (nativeRepresentationComparisonIso p
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.nativeLeftTransportRepresentation p)
        (_root_.SerrePositivity.KST.Fibration.StrictTransportComparisonSpan.representation s.toStrictTransportComparisonSpan)).hom (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex c)) ≫
      (eqToIso (congrArg HomotopyCategory.mk
        (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.ScaffoldTransportComparisonSpan.coefficientResolutionVertexEq (p := p) c))).hom =
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.pointedSpaceLeftResolutionComparison ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.leftStrictTransportFunctor p).obj c)).app
        (Opposite.op ⦋0⦌) (ULift.up v)) := by
  have h := congrArg
    (fun m => m ≫ (eqToIso (congrArg HomotopyCategory.mk
      (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.ScaffoldTransportComparisonSpan.coefficientResolutionVertexEq (p := p) c))).hom)
    ((_root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.nativeCoefficientPointHom s) c v)
  have he := pointedFiberPointHom_endpointTransport
    (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Transport.ScaffoldTransportComparisonSpan.coefficientResolutionVertexEq (p := p) c)
    ((_root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.coefficientWeightedPointedFiberPoint s) c v)
  have hn := ((_root_.SerrePositivity.KST.Fibration.ScaffoldTransportComparisonSpan.coefficientWeightedResolutionPoint_eq s) c v)
  have hr := he.trans (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.cosliceFiberPointHom hn)
  simpa only [Category.assoc] using h.trans hr

end SerrePositivity.KST.Fibration
