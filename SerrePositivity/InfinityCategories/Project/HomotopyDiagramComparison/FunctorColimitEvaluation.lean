module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeCoconeAbsolute
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.FunctorColimitConeExistence

/-!
概要：点ごとの余極限の存在から、元の任意の関手圏の余極限余錐の評価が余極限となることを示す。
方針：元の余錐の評価・prism・全 Hom の普遍性を、厳密な射と同型で照合する。
規約：F2 は読み取り専用。使われ方：HTT 5.5.4.5・5.5.4.11 の強飽和性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 点ごとの余極限が存在すれば、元の任意の余極限余錐の評価も余極限。 -/
lemma isColimitCone_functor_evaluation_of_pointwise_exists {J K X : SSet.{u}}
    [Quasicategory X] {r : J ⟶ (ihom K).obj X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone r) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c)
    (h : ∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorDiagram r k)) (k : K _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanPostcomposeCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k) c) := by
  obtain ⟨d, hd, hdp⟩ := _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CatInfinity.exists_colimitCone_functor_of_pointwise r h
  have e := _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso.map (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitConeIso d c hd hc) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp r (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k))
  exact (hdp k).of_vertexIso e

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
