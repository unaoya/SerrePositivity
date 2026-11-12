module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoherentConstantCoconeComparison
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.InvertibleEdge
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.Homotopy.HomotopyWhiskering

/-!
概要：元の全空間のホモトピックな二射が表す native 余錐全体を比較する。
方針：同じ内部 Hom のホモトピーを持ち上げ、標準余錐比較の充満忠実性で戻す。
規約：元の図式と標的を固定。使われ方：native な積の脚の単位表現の余錐比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- Kan 標的への同じホモトピーの辺を、持ち上げた内部 Hom の頂点同型にする。 -/
def liftedFunctorHomotopyVertexIso {A Z : SSet.{u}} [KanComplex Z] {a b : A ⟶ Z}
    (H : SSet.Homotopy a b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := (SSet.uliftFunctor.{u + 1, u}).obj ((ihom A).obj Z))
      (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex a)) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex b)) := by
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftTruncatedEdge.{u, u + 1} (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorEdgeOfSimplicialHomotopy H)
  have : IsIso (SSet.Truncated.HomotopyCategory.homMk e) :=
    IsGroupoid.all_isIso (C := hoFunctor.obj
      ((SSet.uliftFunctor.{u + 1, u}).obj ((ihom A).obj Z))) _
  exact asIso (SSet.Truncated.HomotopyCategory.homMk e)

/-- ホモトピックな指定射の native 余錐は、同じ余錐空間内で同型。 -/
def constantCoconeHomotopyIso {B : SSet.{u}}
    (F : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})
    (z : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u} _⦋0⦌)
    {a b : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.smallLeftUnstraightening F ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.spaceInfinityObject z).obj}
    (H : SSet.Homotopy a b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso (X := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace F z)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentConstantCocone F z a) z
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentConstantCocone_vertex F z a))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeMappingPointAt (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentConstantCocone F z b) z
        (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentConstantCocone_vertex F z b)) :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coherentCoconeTotalComparison_isQCatEquivalence F z).isFullyFaithful.preimageVertexIso
    (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentConstantCoconeComparisonIso F z a ≪≫
      liftedFunctorHomotopyVertexIso H ≪≫ (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.coherentConstantCoconeComparisonIso F z b).symm)

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
