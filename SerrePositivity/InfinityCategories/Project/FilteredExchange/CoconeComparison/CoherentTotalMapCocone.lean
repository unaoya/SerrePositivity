module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.VertexTransport.FunctorIsoTransport
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.LeftUnstraightening
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraightening
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeFiberValueMap
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeTransformationPoint
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoherentCoconeTotalComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.CoherentConstantCocone
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.CoherentConstantCoconeComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.CoherentTotalMap
public import SerrePositivity.InfinityCategories.HTT.Section3_3_4.CoherentTotalObject
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.LargeTotalCoconeUnit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeMappingSpace

/-!
概要：全空間の射を、元の余極限頂点を持つ指定余錐に接続する。
方針：標的の元の単位との合成を実現し、単位の自然性で像を正規化する。
規約：元の全空間射と単位を保持。使われ方：引き戻しの二射影の余錐表示。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {B C : SSet.{u}}
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (G : (SSet.uliftFunctor.{u + 1, u}).obj C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (a : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening G)

/-- 概要：全空間射の後に標的の単位を続ける元の図式上の余錐。
方針：元の合成を表す native 余錐を実現。
規約：元の標的余極限頂点。使われ方：二射影の余錐表示。 -/
def coherentTotalMapCocone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentConstantCocone F (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G) (a ≫ _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalUnit G)

/-- 概要：写像余錐の頂点は標的の元の余極限頂点。
方針：指定頂点の実現。規約：厳密な等式。使われ方：標準余錐比較への入力。 -/
lemma coherentTotalMapCocone_vertex :
    (coherentTotalMapCocone F G a).vertex = _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentConstantCocone_vertex _ _ _

/-- 概要：写像余錐の標準比較の像は元の単位と余極限頂点の射の合成に同型。
方針：指定射の比較と単位の厳密な自然性。
規約：選んだ余錐と指定射を保持。使われ方：余極限写像の作用の照合。 -/
def coherentTotalMapCoconeComparisonIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := (SSet.uliftFunctor.{u + 1, u}).obj
      ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F)).obj
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G)).obj))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coherentCoconeTotalComparison F (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G)).app (Opposite.op ⦋0⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt (coherentTotalMapCocone F G a) (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G)
          (coherentTotalMapCocone_vertex F G a)))
      (ULift.up.{u + 1, u}
        (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalUnit F ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTotalVertexMap F G a))) := by
  simpa only [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTotalVertexMap_unit, coherentTotalMapCocone] using
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentConstantCoconeComparisonIso F (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G)
      (a ≫ _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalUnit G)

/-- 概要：写像余錐の実際の fiber 評価は元の単位と頂点射の合成に同型。
方針：全空間の比較を保ち、単位の自然性を持ち上げる。
規約：大きい全空間からの実際の射。使われ方：全 Hom の作用比較。 -/
def coherentTotalMapCoconeFiberIso :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeFiberValueMapAt (coherentTotalMapCocone F G a)
      (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G) (coherentTotalMapCocone_vertex F G a))
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentLargeTotalUnit F ≫
        (SSet.uliftFunctor.{u + 1, u}).map (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTotalVertexMap F G a)) := by
  have e := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentConstantCoconeFiberIso F (_root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalVertex G)
    (a ≫ _root_.SerrePositivity.InfinityCategories.HTT.Section3_3_4.coherentDiagramTotalUnit G)
  apply _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e rfl
  rw [← _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentTotalVertexMap_unit, Functor.map_comp]
  rfl

end SerrePositivity.InfinityCategories.Project.FilteredExchange
