module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.IntervalTriangleNaturality
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CompositionTriangleCospan

/-!
概要：元の第一三角形の対角と標的図式の辺を、第二三角形の同じ外ホーンとして束ねる。
方針：同じ合成三角形空間の普遍対角と、元の標的輸送辺を使う。
規約：実際の第二三角形への制限写像も保持する。
使われ方：元の固定成分 Hom fiber の外ホーン延長による pullback 表示。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

variable (F G : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianTransportDiagramCategory (ULift.{u} (Fin 2)))
local notation "c" => (ULift.up (1 : Fin 2))
variable (v : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingSpace (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue F c))
  (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianTransportDiagramValue G c))) _⦋0⦌)
local notation "E" => (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianHomIntervalEvaluation F G c) v)

/-- 元の第一三角形から、第二三角形の対角・標的辺を固定する外ホーンへ写す。 -/
def cocartesianIntervalOuterHornMap :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalCompositionSpace F G v ⟶
      (ihom (horn 2 2 : SSet.{u + 1})).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.compositionTriangleCospanMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalCompositionFirstEdge F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex v) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalCompositionFirstEdge G)

/-- 元の固定成分 fiber の、同じ第二三角形への実際の制限写像。 -/
def cocartesianIntervalSecondTriangleMap : E ⟶ (ihom (Δ[2] : SSet.{u + 1})).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity.{u} :=
  curry (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalHomTriangle F G v 1 (𝟙 E))

/-- 第二三角形への同じ普遍制限写像も、任意の族で元の第二三角形を回収する。 -/
lemma cocartesianIntervalSecondTriangleMap_uncurry {T : SSet.{u + 1}} (f : T ⟶ E) :
    uncurry (f ≫ cocartesianIntervalSecondTriangleMap F G v) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalHomTriangle F G v 1 f := by
  unfold cocartesianIntervalSecondTriangleMap
  rw [uncurry_natural_left, uncurry_curry, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalHomTriangle_precomp,
    Category.comp_id]

/-- 元の第二三角形の標的側の辺は、元の標的輸送辺に全パラメーターで定値。 -/
lemma cocartesianIntervalSecondTriangle_target {T : SSet.{u + 1}} (f : T ⟶ E) :
    (stdSimplex.δ (0 : Fin 3) ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalHomTriangle F G v 1 f =
      fst (Δ[1] : SSet.{u + 1}) T ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalCompositionFirstEdge G).edge := by
  unfold _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalHomTriangle
  rw [← Category.assoc, ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.triangleSquare_lower_right,
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalHomSquare_one, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalCompositionFirstEdge_map]

/-- 同じ外ホーンの対角は、任意の全パラメーターでも元の第一三角形の対角。 -/
lemma cocartesianIntervalOuterHornMap_diagonal {T : SSet.{u + 1}}
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalCompositionSpace F G v) :
    (horn₂₂.ι₀₂ ▷ T) ≫ uncurry (a ≫ cocartesianIntervalOuterHornMap F G v) =
      (stdSimplex.δ (1 : Fin 3) ▷ T) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.innerTriangleExtensionUncurry a :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.compositionTriangleCospanMap_diagonal _ _ _ a

/-- 同じ外ホーンの標的辺は、任意の族でも元の標的輸送辺に定値。 -/
lemma cocartesianIntervalOuterHornMap_target {T : SSet.{u + 1}}
    (a : T ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalCompositionSpace F G v) :
    (horn₂₂.ι₁₂ ▷ T) ≫ uncurry (a ≫ cocartesianIntervalOuterHornMap F G v) =
      fst (Δ[1] : SSet.{u + 1}) T ≫
        SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianIntervalCompositionFirstEdge G).edge :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.compositionTriangleCospanMap_target _ _ _ a

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
