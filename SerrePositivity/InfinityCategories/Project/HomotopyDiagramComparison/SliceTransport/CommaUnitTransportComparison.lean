module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.CommaUnitTransportEndpoint
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InitialParametrizedPointTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.DiagonalFiberTransport

/-!
概要：標準単位比較を、同じ comma 頂点からの普遍輸送と関手同型で照合する。
方針：元の合成円柱の始点・終点・底を指定し、left fibration の輸送の一意性を使う。
規約：単位の普遍性を仮定しない。使われ方：始対象条件から写像空間の単位比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable {X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
variable {F : X ⟶ Y} {G : Y ⟶ X}

/-- 元の合成円柱の終点は、同じ指定単位頂点で評価した普遍輸送と関手同型。 -/
def unitCommaCompositionEndpoint_transportIso (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G))
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitCommaCompositionEndpoint η x y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.parametrizedFiberTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection G x)
        (F.app (Opposite.op ⦋0⦌) x) y ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitCommaSectionTargetFiberVertex η x)) := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection G x
  let v := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitCommaSectionTargetFiberVertex η x
  let P := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (F.app (Opposite.op ⦋0⦌) x) y
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingCurryOfEndpoints (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (𝟙 P))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamily_zero (𝟙 P)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamily_one (𝟙 P)) = 𝟙 P := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_curryOfEndpoints _ _ _
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibrationPrism_diagonalTransportIso p
    (SSet.const v : P ⟶ _) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitCommaCompositionEndpoint η x y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (𝟙 P)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamily_zero (𝟙 P))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamily_one (𝟙 P)) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitCommaCompositionPrism η x y)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitCommaCompositionPrism_zero η x y)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitCommaCompositionEndpoint_ι η x y).symm
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitCommaCompositionPrism_projection η x y)
  rw [hc] at e
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.diagonalFiberTransport p (SSet.const v : P ⟶ _) (𝟙 P) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.parametrizedFiberTransport p (F.app (Opposite.op ⦋0⦌) x) y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v := by
    change lift (SSet.const v) (𝟙 P) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.parametrizedFiberTransportFamily p (F.app (Opposite.op ⦋0⦌) x) y).endpoint =
      curry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.parametrizedFiberTransportFamily p (F.app (Opposite.op ⦋0⦌) x) y).endpoint ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex]
  rw [hd] at e
  exact e

/-- 指定単位比較そのものは、同じ単位頂点からの普遍輸送を区間模型へ移した射。 -/
def unitIntervalMap_commaTransportIso (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G))
    (x : X _⦋0⦌) (y : Y _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalMap η x y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.parametrizedFiberTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection G x)
        (F.app (Opposite.op ⦋0⦌) x) y ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitCommaSectionTargetFiberVertex η x) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberToInterval G x y) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitCommaCompositionEndpoint_interval, Category.assoc] using
    (unitCommaCompositionEndpoint_transportIso η x y).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberToInterval G x y)

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
