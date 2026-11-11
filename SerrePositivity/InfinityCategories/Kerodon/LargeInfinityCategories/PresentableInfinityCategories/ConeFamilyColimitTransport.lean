module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ConeFamilyStrictification
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.VertexConeIsoTransport
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.CoherentTotalColimit
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.FunctorPointwiseColimitCriterion
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanDiagramColimitTransport
public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorColimitEvaluation

/-!
概要：共同 strictification の全錐族へ、元の点ごとの余極限を指定頂点のまま輸送する。
方針：全図式の関手同型に沿う native な余錐の輸送と、Space の点ごとの余極限の存在を使う。
規約：元の全錐の頂点を等号で保持し、各段階の極限性も同じ大域同型から回収する。
使われ方：strict な極限保存から元の任意の coherent 錐族への帰還。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

variable {I J : Type u} [SmallCategory I] [SmallCategory J]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶
    (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u + 1})
      ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)))).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})

/-- 各段階の全錐の極限性は、共同 strictification の同じ段階へ保存・反映される。 -/
lemma coneFamilyStrictification_stage_isLimit_iff (j : J) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFamilyStrictRealization F).app
      (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex j)))) ↔
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone (F.app
      (Opposite.op ⦋0⦌) (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex j)))) :=
  _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.isLimitCone_functorVertexCone_iff_of_vertexIso
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFamilyStrictificationIso F).app (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex j)))

/-- 元の指定点ごとの余極限余錐を、同じ頂点のまま同時 strict 化した族へ輸送する。 -/
def coneFamilyStrictColimitCocone (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) (hc : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.IsPointwiseColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFamilyStrictRealization F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.colimitCoconeOfFunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFamilyStrictificationIso F).symm c
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isColimitCone_of_pointwise c hc)

/-- 輸送された一つの全余錐は、同時 strict 化した元の族の点ごとの余極限である。 -/
lemma coneFamilyStrictColimitCocone_pointwise (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F)
    (hc : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.IsPointwiseColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.IsPointwiseColimitCone (coneFamilyStrictColimitCocone F c hc) := by
  intro k
  exact _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.isColimitCone_functor_evaluation_of_pointwise_exists _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.colimitCoconeOfFunctorIso_isColimit _ c (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isColimitCone_of_pointwise c hc))
    (fun k ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimitsOfSpaces.hasColimit_coherentSpaceDiagram
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.evaluateFunctorDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFamilyStrictRealization F) k)) k

/-- 輸送後の完成した全錐は、元の完成した全錐そのものを頂点に持つ。 -/
lemma coneFamilyStrictColimitCocone_vertex (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F)
    (hc : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.IsPointwiseColimitCone c) :
    (coneFamilyStrictColimitCocone F c hc).vertex = c.vertex :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.colimitCoconeOfFunctorIso_vertex _ c (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isColimitCone_of_pointwise c hc)

/-- 完成後の全錐の極限性も、同じ指定頂点を保持した輸送によって保存・反映される。 -/
lemma coneFamilyStrictColimitCocone_isLimit_iff (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F)
    (hc : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.IsPointwiseColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone (coneFamilyStrictColimitCocone F c hc).vertex) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone c.vertex) := by
  rw [coneFamilyStrictColimitCocone_vertex]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
