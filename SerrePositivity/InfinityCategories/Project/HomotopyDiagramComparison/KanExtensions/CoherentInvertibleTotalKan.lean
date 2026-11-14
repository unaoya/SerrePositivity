module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.Homotopies.CoherentDiagrams.CoherentInvertibleTotalMap
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.KanExtensions.TotalKanNativeCoconeComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ContinuousKanWeakFunctoriality
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.WeakHomotopyInverse

/-!
概要：元の可逆変換の全空間作用を、元の余極限 Kan 模型の指定同値辺へ移す。
方針：前合成同値の弱同値性を Kan 置換へ移し、元の辺と全余錐作用を保持する。
規約：底の quasicategory 性は不要。単位と元の余極限余錐を変更しない。
使われ方：元の P_Σ 評価錐と反復積錐の比較の余極限への移送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
variable {B : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G) _⦋0⦌)

/-- 元の指定全空間作用の、元の余極限 Kan 模型間の Kan 像。 -/
def coherentTransformationTotalKanMap : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan F ⟶
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentDiagramTotalKan G :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacement.map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap F G t)

/-- 同じ Kan 像は、元の両全空間の置換単位と厳密に可換。 -/
lemma coherentTransformationTotalKanMap_unit :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F) ≫
      coherentTransformationTotalKanMap F G t =
        _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap F G t ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.app (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening G) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.continuousKanReplacementUnit.naturality _).symm

/-- 元の可逆変換の Kan 像には実際の単体的ホモトピー逆がある。 -/
lemma coherentInvertibleTotalKanMap_homotopyEquivalence
    (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex t)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsSimplicialHomotopyEquivalence (coherentTransformationTotalKanMap F G t) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.continuousKanReplacement_map_isWeakHomotopyEquivalence _
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentInvertibleTotalMap_isPrecompositionEquivalence F G t ht).isWeakHomotopyEquivalence
      ).isSimplicialHomotopyEquivalence

/-- 同じ Kan 像の元の coherent 辺は可逆である。 -/
lemma coherentInvertibleTotalKanNativeEdge_isInvertible
    (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.intervalMappingEdgeOfVertex t)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanNativeEdge F G (coherentTransformationTotalKanMap F G t)) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr (e :=
    (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanNativeEdge F G (coherentTransformationTotalKanMap F G t)).toTruncated)
    (f := (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge (C := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.KanObject.{u})
      (X := _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalKanObject F) (Y := _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalKanObject G)
      (coherentTransformationTotalKanMap F G t)).toTruncated) rfl).mpr
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.coherentKanEdge_isInvertible_of_isQCatEquivalence
    (coherentInvertibleTotalKanMap_homotopyEquivalence F G t ht).isQCatEquivalence

/-- 元の同じ可逆比較辺による全余錐作用は、元の指定 Kan 射の単位表現に一致する。 -/
def coherentTransformationTotalKanNativeCoconeIso :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.totalKanNativeCoconeIso F G (coherentTransformationTotalKanMap F G t)

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
