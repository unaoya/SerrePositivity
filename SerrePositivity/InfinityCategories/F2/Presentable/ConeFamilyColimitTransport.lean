module

public import SerrePositivity.InfinityCategories.F2.Presentable.ConeFamilyStrictification
public import SerrePositivity.InfinityCategories.F2.VertexConeIsoTransport
public import SerrePositivity.InfinityCategories.F2.CoherentTotalColimit
public import SerrePositivity.InfinityCategories.F2.FunctorPointwiseColimitCriterion
public import SerrePositivity.InfinityCategories.HomotopyLimits.KanDiagramColimitTransport
public import SerrePositivity.InfinityCategories.HomotopyLimits.FunctorColimitEvaluation

/-!
概要：共同 strictification の全錐族へ、元の点ごとの余極限を指定頂点のまま輸送する。
方針：全図式の関手同型に沿う native な余錐の輸送と、Space の点ごとの余極限の存在を使う。
規約：元の全錐の頂点を等号で保持し、各段階の極限性も同じ大域同型から回収する。
使われ方：strict な極限保存から元の任意の coherent 錐族への帰還。
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
variable {I J : Type u} [SmallCategory I] [SmallCategory J]
  (F : (SSet.uliftFunctor.{u + 1, u}).obj (nerve J) ⟶
    (ihom (join (Δ[0] : SSet.{u + 1})
      ((SSet.uliftFunctor.{u + 1, u}).obj (nerve I)))).obj SpaceInfinity.{u})

/-- 各段階の全錐の極限性は、共同 strictification の同じ段階へ保存・反映される。 -/
lemma coneFamilyStrictification_stage_isLimit_iff (j : J) :
    IsLimitCone (functorVertexCone ((coneFamilyStrictRealization F).app
      (Opposite.op ⦋0⦌) (ULift.up (nerveVertex j)))) ↔
    IsLimitCone (functorVertexCone (F.app
      (Opposite.op ⦋0⦌) (ULift.up (nerveVertex j)))) :=
  isLimitCone_functorVertexCone_iff_of_vertexIso
    ((coneFamilyStrictificationIso F).app (ULift.up (nerveVertex j)))

/-- 元の指定点ごとの余極限余錐を、同じ頂点のまま同時 strict 化した族へ輸送する。 -/
def coneFamilyStrictColimitCocone (c : JoinCocone F) (hc : IsPointwiseColimitCone c) :
    JoinCocone (coneFamilyStrictRealization F) :=
  colimitCoconeOfFunctorIso (coneFamilyStrictificationIso F).symm c
    (isColimitCone_of_pointwise c hc)

/-- 輸送された一つの全余錐は、同時 strict 化した元の族の点ごとの余極限である。 -/
lemma coneFamilyStrictColimitCocone_pointwise (c : JoinCocone F)
    (hc : IsPointwiseColimitCone c) :
    IsPointwiseColimitCone (coneFamilyStrictColimitCocone F c hc) := by
  intro k
  exact isColimitCone_functor_evaluation_of_pointwise_exists _
    (colimitCoconeOfFunctorIso_isColimit _ c (isColimitCone_of_pointwise c hc))
    (fun k ↦ hasColimit_coherentSpaceDiagram
      (evaluateFunctorDiagram (coneFamilyStrictRealization F) k)) k

/-- 輸送後の完成した全錐は、元の完成した全錐そのものを頂点に持つ。 -/
lemma coneFamilyStrictColimitCocone_vertex (c : JoinCocone F)
    (hc : IsPointwiseColimitCone c) :
    (coneFamilyStrictColimitCocone F c hc).vertex = c.vertex :=
  colimitCoconeOfFunctorIso_vertex _ c (isColimitCone_of_pointwise c hc)

/-- 完成後の全錐の極限性も、同じ指定頂点を保持した輸送によって保存・反映される。 -/
lemma coneFamilyStrictColimitCocone_isLimit_iff (c : JoinCocone F)
    (hc : IsPointwiseColimitCone c) :
    IsLimitCone (functorVertexCone (coneFamilyStrictColimitCocone F c hc).vertex) ↔
      IsLimitCone (functorVertexCone c.vertex) := by
  rw [coneFamilyStrictColimitCocone_vertex]

end SerrePositivity.InfinityCategories.F2.Presentable
