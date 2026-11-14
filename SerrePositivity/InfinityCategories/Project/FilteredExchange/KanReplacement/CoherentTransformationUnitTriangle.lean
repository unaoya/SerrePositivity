module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.InnerFibrations.InnerFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.PointedSpaces
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.TransformationFamilyDiagram
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CartesianFibration
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraightening
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.LeftUnstraighteningFiberValue
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningMappingInvertible
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningTransformationFamily
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraightening
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Kan
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoherentSmallConstantTarget
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.ConstantDiagramTransportWitness
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.CoherentConstantRepresentationLarge
public import SerrePositivity.InfinityCategories.HTT.Section3_3_4.CoherentTotalObject
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.CoherentTotalUnitRepresentation
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.CoherentTransformationVertexTriangle
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.LargeTotalCoconeUnit
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.GrothendieckConstruction.UnstraighteningTriangleVertex

/-!
概要：元の coherent 変換と標的の指定単位を全三角形で合成する。
方針：三角形の全空間合成比較に、元の単位の指定表現同型を続ける。
規約：元の二辺と選択済み三角形を保持。使われ方：元の変換による余錐の表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {B : SSet.{u}}
  (F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (t : (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningTransformationSpace F G) _⦋0⦌)

/-- 概要：元の変換と標的の単位を結ぶ全三角形の型。
方針：指定二辺を元の変換と元の単位の表現に固定。
規約：長辺と三つの制限も保持。使われ方：同じ三角形での指定比較。 -/
abbrev CoherentTransformationUnitTriangle :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTransformationVertexTriangle F G (SSet.const (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G)) t
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTotalUnitRepresentation G).1

/-- 概要：元の変換と元の単位の合成三角形を全データ付きで選ぶ。
方針：二辺固定の三角形充填。規約：単位を選び直さない。使われ方：指定余錐の回収。 -/
def coherentTransformationUnitTriangle : CoherentTransformationUnitTriangle F G t :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationVertexTriangle F G (SSet.const (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G)) t
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTotalUnitRepresentation G).1

/-- 概要：元の合成三角形の長辺の全空間射は元の変換の作用と元の単位の合成に同型。
方針：指定三角形の全空間比較に元の単位の表現同型を前合成して続ける。
規約：任意の指定済み三角形の比較。使われ方：元の余錐の標準比較への移送。 -/
def coherentTransformationUnitTriangleLargeIso (T : CoherentTransformationUnitTriangle F G t) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingVertexMap F (SSet.const (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G))
        T.diagonal).val ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantUnstraighteningFiberProjection _ (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G) ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberValueEquivalence (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G)).hom)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingVertexMap F G t).val ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentLargeTotalUnit G) := by
  have e := (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.unstraighteningTriangleVertexIso F G
    (SSet.const (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G)) t (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTotalUnitRepresentation G).1
    T.diagonal T.diagram T.first T.second T.long).postcomp
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.constantUnstraighteningFiberProjection _ (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.pointedSpaceFiberValueEquivalence (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G)).hom)
  have eu := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentConstantRepresentation.largeIso G (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G)
    (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalUnit G) (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTotalUnitRepresentation G)
  exact e ≪≫ eu.precomp (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.leftUnstraighteningMappingVertexMap F G t).val

end SerrePositivity.InfinityCategories.Project.FilteredExchange
