module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.KanFamilyRealizedColimit
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.KanFamilyJointRealization
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PointwiseColimitPrecomposition
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ConeFamilyStageComparison
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.PointwiseColimitChoiceTransport

/-!
概要：共同 strict 模型の指定余極限図式を、元の strict 化した全錐族の点ごとの native 余極限として公開する。
方針：同じ全余錐を実現し、全単体の族の等式と錐形状の宇宙同型で元の型へ戻す。
規約：頂点は元の strict 余極限図式の錐形状による実現そのもの。
使われ方：元の指定された余極限余錐と、極限性を検証した strict 模型の同定。

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

variable {I J : Type u} [SmallCategory I] [SmallCategory J] [IsFiltered J]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶
    (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{u + 1})
      ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)))).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{u})

/-- 実現した共同模型を元の錐形状で読む全図式族。 -/
def coneFamilyModelDiagram :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentDiagram
      ((CategoryTheory.Functor.curry.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFamilyStrictification F)) ⋙ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kanDiagramBundle) ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.kanDiagramRealization (WithInitial I)) ≫
      (pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.uliftInitialConeIso I).inv).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity

omit [IsFiltered J] in
/-- 同じ共同模型の実現は、元の strict 化した全錐族と全単体で一致する。 -/
lemma coneFamilyModelDiagram_eq : coneFamilyModelDiagram F = _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFamilyStrictRealization F := by
  unfold coneFamilyModelDiagram
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kanFamily_realization_curry, CategoryTheory.Functor.uncurry_obj_curry_obj]
  rfl

/-- 元の strict 化した全錐族に対する、同じ共同模型の指定余極限余錐。 -/
def coneFamilyModelColimitCocone : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFamilyStrictRealization F) :=
  _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq (coneFamilyModelDiagram_eq F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.uliftInitialConeIso I).inv).app _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kanFamilyRealizedColimitCocone
        (CategoryTheory.Functor.curry.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFamilyStrictification F))))

/-- 同じ共同模型の指定全余錐は、元の strict 化した全錐族の点ごとの native 余極限。 -/
lemma coneFamilyModelColimitCocone_pointwise :
    _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.IsPointwiseColimitCone (coneFamilyModelColimitCocone F) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pointwiseColimitCocone_diagramEq
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pointwiseColimitCocone_precomp
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kanFamilyRealizedColimitCocone_pointwise _

/-- 完成した全錐の頂点は、同じ元の関手圏の strict 余極限図式の実現そのもの。 -/
lemma coneFamilyModelColimitCocone_vertex :
    (coneFamilyModelColimitCocone F).vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.uliftInitialConeIso I).inv ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.kanDiagramCoherentNerve
        (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cardinalFilteredKanDiagram
          (CategoryTheory.Functor.curry.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFamilyStrictification F)))) := by
  rw [coneFamilyModelColimitCocone, _root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.coherentCoconeOfDiagramEq_vertex,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.mapJoinCocone_vertex, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.kanFamilyRealizedColimitCocone_vertex]
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ _).symm.injective
  rw [_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexMap_precomp]
  erw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- 模型の完成した全錐の極限性は、元の指定余極限余錐の完成した全錐の極限性と同値。 -/
lemma coneFamilyModelCompletedLimit_iff (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) (hc : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.IsPointwiseColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone (coneFamilyModelColimitCocone F).vertex) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone c.vertex) :=
  (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.pointwiseColimitCompletedLimit_iff (coneFamilyModelColimitCocone F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFamilyStrictColimitCocone F c hc) (coneFamilyModelColimitCocone_pointwise F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFamilyStrictColimitCocone_pointwise F c hc)).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFamilyStrictColimitCocone_isLimit_iff F c hc)

/-- 元の指定余極限で完成した錐の極限性を、同じ strict 余極限図式の N の錐で検出する。 -/
lemma coneFamilyModelStrictLimit_iff [Quiver.IsThin I]
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) (hc : _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.IsPointwiseColimitCone c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.strictCoherentCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.withInitialKanCone
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.cardinalFilteredKanDiagram
        (CategoryTheory.Functor.curry.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.coneFamilyStrictification F))))) ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone c.vertex) := by
  have h := coneFamilyModelCompletedLimit_iff F c hc
  rw [coneFamilyModelColimitCocone_vertex] at h
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.withInitialKanCone_isLimit_iff _).symm.trans h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
