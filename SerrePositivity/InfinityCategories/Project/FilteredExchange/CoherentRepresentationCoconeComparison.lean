module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.EquivalenceFullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.FullyFaithful
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.PrecompositionEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinity
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.Vertices
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.SmallLeftUnstraightening
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InnerFibration
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeTransformationPoint
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoherentCoconeTotalComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentRepresentationCocone
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentTotalUnitRepresentation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeMappingSpace

/-!
概要：同じ指定全空間射を表す二つの元の native 余錐を比較する。
方針：元の標準全空間比較の充満忠実性で指定された二つの比較同型を反映する。
規約：両方の表現と余錐を保持。使われ方：元の三角形の長辺と元の写像余錐の照合。
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
  (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
  (z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)
  (a : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject z).obj)

/-- 概要：同じ指定射の二表現の元の余錐の間の比較同型。
方針：標準比較の像で指定射を介して結び、充満忠実性で元の余錐へ戻す。
規約：元の二余錐の指定頂点を保持。使われ方：元の合成三角形の余錐比較。 -/
def coherentRepresentationCoconeIso (R S : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentConstantRepresentation F z a) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F z)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentRepresentationCocone F z a R) z
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentRepresentationCocone_vertex F z a R))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentRepresentationCocone F z a S) z
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentRepresentationCocone_vertex F z a S)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coherentCoconeTotalComparison_isQCatEquivalence F z).isFullyFaithful.preimageVertexIso
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentRepresentationCoconeComparisonIso F z a R ≪≫
      (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentRepresentationCoconeComparisonIso F z a S).symm)

end SerrePositivity.InfinityCategories.Project.FilteredExchange
