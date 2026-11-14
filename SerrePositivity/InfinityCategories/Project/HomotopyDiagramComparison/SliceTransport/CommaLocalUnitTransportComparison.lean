module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.SliceTransport.CommaLocalUnitTransportEndpoint

/-!
概要：局所区間比較を同じ comma 点からの普遍輸送と関手同型で照合する。
方針：元の円柱の始点・終点・底を指定し、left fibration の輸送の一意性を使う。
規約：始点は元の点であり、底は Y の普遍区間族そのもの。
使われ方：局所比較と普遍輸送の関手同型の入力。
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
variable {G : Y ⟶ X} {x : X _⦋0⦌} {y₀ : Y _⦋0⦌}

/-- 概要：局所円柱の終点と点で評価した普遍輸送の関手同型。
方針：left fibration の円柱輸送の一意性を使う。
規約：元の点 v と普遍区間族を保持。
使われ方：区間比較の輸送表示。 -/
def unitCommaCompositionEndpointAt_transportIso
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection G x) y₀) _⦋0⦌)
    (y : Y _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitCommaCompositionEndpointAt v y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.parametrizedFiberTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection G x)
        y₀ y ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v) := by
  let p := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection G x
  let P := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace y₀ y
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingCurryOfEndpoints (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (𝟙 P))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamily_zero (𝟙 P)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamily_one (𝟙 P)) = 𝟙 P := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_injective
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry_curryOfEndpoints _ _ _
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.leftFibrationPrism_diagonalTransportIso p
    (SSet.const v : P ⟶ _) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitCommaCompositionEndpointAt v y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingUncurry (𝟙 P)) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamily_zero (𝟙 P))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.intervalFamily_one (𝟙 P)) (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitCommaCompositionPrismAt v y)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitCommaCompositionPrismAt_zero v y)
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitCommaCompositionEndpointAt_ι v y).symm
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitCommaCompositionPrismAt_projection v y)
  rw [hc] at e
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.diagonalFiberTransport p (SSet.const v : P ⟶ _) (𝟙 P) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.parametrizedFiberTransport p y₀ y ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v := by
    change lift (SSet.const v) (𝟙 P) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.parametrizedFiberTransportFamily p y₀ y).endpoint =
      curry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.parametrizedFiberTransportFamily p y₀ y).endpoint ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.FibrationsOverOrdinaryCategories.curry_evaluateFunctorAt_vertex]
  rw [hd] at e
  exact e

/-- 概要：局所区間比較と元の点からの普遍輸送の関手同型。
方針：終点の輸送同型を区間模型へ後合成する。
規約：F と大域単位を引数に取らない。
使われ方：E2 の局所写像空間条件。 -/
def unitIntervalMapAt_commaTransportIso
    (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection G x) y₀) _⦋0⦌)
    (y : Y _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitIntervalMapAt v y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.parametrizedFiberTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection G x)
        y₀ y ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt v ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberToInterval G x y) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitCommaCompositionEndpointAt_interval, Category.assoc] using
    (unitCommaCompositionEndpointAt_transportIso v y).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberToInterval G x y)

/-- 概要：指定単位の点への特殊化を既存の比較写像の型で供給する。
方針：局所輸送同型の始域を厳密な特殊化の等式で書き換える。
規約：既存の単位版の宣言と比較写像の選択は変更しない。
使われ方：F と単位を持つ利用者が局所版をそのまま使う。 -/
def unitIntervalMapAt_commaTransportIso_unit {F : X ⟶ Y}
    (η : _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom (𝟙 X) (F ≫ G)) (a : X _⦋0⦌) (y : Y _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitIntervalMap η a y)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.parametrizedFiberTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberProjection G a)
        (F.app (Opposite.op ⦋0⦌) a) y ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitCommaSectionTargetFiberVertex η a) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.AdjointFunctorsBetweenInfinityCategories.unitCommaFiberToInterval G a y) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitIntervalMapAt_unitCommaSectionTargetFiberVertex] using
    unitIntervalMapAt_commaTransportIso (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.unitCommaSectionTargetFiberVertex η a) y


end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
