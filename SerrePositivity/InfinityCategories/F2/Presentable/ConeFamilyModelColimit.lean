module

public import SerrePositivity.InfinityCategories.F2.Presentable.KanFamilyRealizedColimit
public import SerrePositivity.InfinityCategories.F2.Presentable.KanFamilyJointRealization
public import SerrePositivity.InfinityCategories.F2.Presentable.PointwiseColimitPrecomposition
public import SerrePositivity.InfinityCategories.F2.Presentable.ConeFamilyStageComparison
public import SerrePositivity.InfinityCategories.F2.PointwiseColimitChoiceTransport

/-!
概要：共同 strict 模型の指定余極限図式を、元の strict 化した全錐族の点ごとの native 余極限として公開する。
方針：同じ全余錐を実現し、全単体の族の等式と錐形状の宇宙同型で元の型へ戻す。
規約：頂点は元の strict 余極限図式の錐形状による実現そのもの。
使われ方：元の指定された余極限余錐と、極限性を検証した strict 模型の同定。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable
open HomotopyLimits
variable {I J : Type u} [SmallCategory I] [SmallCategory J] [IsFiltered J]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶
    (ihom (join (Δ[0] : SSet.{u + 1})
      ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)))).obj SpaceInfinity.{u})

/-- 実現した共同模型を元の錐形状で読む全図式族。 -/
def coneFamilyModelDiagram :=
  (strictCoherentDiagram
      ((CategoryTheory.Functor.curry.obj (coneFamilyStrictification F)) ⋙ kanDiagramBundle) ≫
    kanDiagramRealization (WithInitial I)) ≫
      (pre (uliftInitialConeIso I).inv).app SpaceInfinity

omit [IsFiltered J] in
/-- 同じ共同模型の実現は、元の strict 化した全錐族と全単体で一致する。 -/
lemma coneFamilyModelDiagram_eq : coneFamilyModelDiagram F = coneFamilyStrictRealization F := by
  unfold coneFamilyModelDiagram
  rw [kanFamily_realization_curry, CategoryTheory.Functor.uncurry_obj_curry_obj]
  rfl

/-- 元の strict 化した全錐族に対する、同じ共同模型の指定余極限余錐。 -/
def coneFamilyModelColimitCocone : JoinCocone (coneFamilyStrictRealization F) :=
  coherentCoconeOfDiagramEq (coneFamilyModelDiagram_eq F)
    (mapJoinCocone ((pre (uliftInitialConeIso I).inv).app SpaceInfinity)
      (kanFamilyRealizedColimitCocone
        (CategoryTheory.Functor.curry.obj (coneFamilyStrictification F))))

/-- 同じ共同模型の指定全余錐は、元の strict 化した全錐族の点ごとの native 余極限。 -/
lemma coneFamilyModelColimitCocone_pointwise :
    IsPointwiseColimitCone (coneFamilyModelColimitCocone F) := by
  apply pointwiseColimitCocone_diagramEq
  apply pointwiseColimitCocone_precomp
  exact kanFamilyRealizedColimitCocone_pointwise _

/-- 完成した全錐の頂点は、同じ元の関手圏の strict 余極限図式の実現そのもの。 -/
lemma coneFamilyModelColimitCocone_vertex :
    (coneFamilyModelColimitCocone F).vertex = functorVertex
      ((uliftInitialConeIso I).inv ≫ kanDiagramCoherentNerve
        (cardinalFilteredKanDiagram
          (CategoryTheory.Functor.curry.obj (coneFamilyStrictification F)))) := by
  rw [coneFamilyModelColimitCocone, coherentCoconeOfDiagramEq_vertex,
    Ind.mapJoinCocone_vertex, kanFamilyRealizedColimitCocone_vertex]
  apply (functorVertexEquiv _ _).symm.injective
  rw [functorVertexMap_precomp]
  erw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

/-- 模型の完成した全錐の極限性は、元の指定余極限余錐の完成した全錐の極限性と同値。 -/
lemma coneFamilyModelCompletedLimit_iff (c : JoinCocone F) (hc : IsPointwiseColimitCone c) :
    IsLimitCone (functorVertexCone (coneFamilyModelColimitCocone F).vertex) ↔
      IsLimitCone (functorVertexCone c.vertex) :=
  (pointwiseColimitCompletedLimit_iff (coneFamilyModelColimitCocone F)
    (coneFamilyStrictColimitCocone F c hc) (coneFamilyModelColimitCocone_pointwise F)
    (coneFamilyStrictColimitCocone_pointwise F c hc)).trans
      (coneFamilyStrictColimitCocone_isLimit_iff F c hc)

/-- 元の指定余極限で完成した錐の極限性を、同じ strict 余極限図式の N の錐で検出する。 -/
lemma coneFamilyModelStrictLimit_iff [Quiver.IsThin I]
    (c : JoinCocone F) (hc : IsPointwiseColimitCone c) :
    IsLimitCone (strictCoherentCone (withInitialKanCone
      (cardinalFilteredKanDiagram
        (CategoryTheory.Functor.curry.obj (coneFamilyStrictification F))))) ↔
      IsLimitCone (functorVertexCone c.vertex) := by
  have h := coneFamilyModelCompletedLimit_iff F c hc
  rw [coneFamilyModelColimitCocone_vertex] at h
  exact (withInitialKanCone_isLimit_iff _).symm.trans h

end SerrePositivity.InfinityCategories.F2.Presentable
