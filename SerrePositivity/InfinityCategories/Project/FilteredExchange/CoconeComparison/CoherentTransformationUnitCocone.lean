module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceLeft
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraighteningTransformationFamily
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraightening
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeTransformationPoint
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.CoherentConstantCocone
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.CoherentRepresentationCocone
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.CoherentRepresentationCoconeComparison
public import SerrePositivity.InfinityCategories.HTT.Section3_3_4.CoherentTotalCocone
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.CoherentTotalMapCocone
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.CoherentTotalMapNative
public import SerrePositivity.InfinityCategories.HTT.Section3_3_4.CoherentTotalObject
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.CoherentTransformationTotalMap
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.CoherentTransformationUnitRepresentation
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.CoherentTransformationUnitTriangle
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconePointHomFamily
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeMappingSpace

/-!
概要：元の変換と単位の合成三角形を native 余錐・余極限写像の表示へ接続する。
方針：元の長辺の表現から余錐を実現し、同じ全空間射の二表現を比較する。
規約：元の三角形を保持。使われ方：元の coherent 変換による余極限写像の照合。
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
  (T : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTransformationUnitTriangle F G t)

/-- 概要：元の変換と指定単位の同じ三角形の長辺を実現した native 余錐。
方針：長辺の指定表現を実現。規約：元の三角形を保持。使われ方：写像余錐との照合。 -/
def coherentTransformationUnitCocone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentRepresentationCocone F (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap F G t ≫ _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalUnit G)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationUnitRepresentation F G t T)

/-- 概要：元の合成三角形の余錐の頂点は標的の元の余極限頂点。
方針：長辺の実現の頂点式。規約：厳密な等式。使われ方：余錐の比較点。 -/
lemma coherentTransformationUnitCocone_vertex :
    (coherentTransformationUnitCocone F G t T).vertex = _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentRepresentationCocone_vertex _ _ _ _

/-- 概要：元の三角形からの余錐は元の全空間写像からの指定余錐と同型。
方針：同じ指定射の二表現の標準比較の充満忠実性。
規約：元の二余錐・三角形を保持。使われ方：native 余極限写像の元の図式との整合。 -/
def coherentTransformationUnitCoconeIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt (coherentTransformationUnitCocone F G t T)
        (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G) (coherentTransformationUnitCocone_vertex F G t T))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTotalMapCocone F G (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap F G t))
        (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G)
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTotalMapCocone_vertex F G (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap F G t))) :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentRepresentationCoconeIso F (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap F G t ≫ _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalUnit G)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationUnitRepresentation F G t T)
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentConstantRepresentation F (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G)
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap F G t ≫ _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalUnit G))

/-- 概要：元の native 余極限写像が表す余錐は元の変換と単位の合成三角形の余錐に同型。
方針：元の native 写像の表示を、同じ全空間射を表す二余錐の比較へ続ける。
規約：選択済み native 写像と元の三角形を保持。使われ方：元の二射影の余極限写像。 -/
def coherentTransformationNativeCoconeIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconePointHomFamily (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalCocone F)
        (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G)).app (Opposite.op ⦋0⦌)
          (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTotalMapNativeRepresentation F G (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap F G t)).1)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt (coherentTransformationUnitCocone F G t T)
        (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G) (coherentTransformationUnitCocone_vertex F G t T)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTotalMapNativeRepresentation F G (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTransformationTotalMap F G t)).2 ≪≫
    (coherentTransformationUnitCoconeIso F G t T).symm

end SerrePositivity.InfinityCategories.Project.FilteredExchange
