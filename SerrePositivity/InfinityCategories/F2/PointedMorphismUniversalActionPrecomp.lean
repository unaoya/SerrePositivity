module

public import SerrePositivity.InfinityCategories.F2.PointedValueMorphismUniversalAction
public import SerrePositivity.InfinityCategories.F2.SpaceSimplexPointedRestrictionNaturality
public import SerrePositivity.InfinityCategories.F2.FunctorIsoWhiskerAlgebra

/-!
概要：元の指定右作用比較の実前合成を、元の全 Hom 成分の同じ前合成の値へ戻す。
方針：実端点の表示変更は同じ前合成のホモトピー圏の像でも保持される。
規約：元の指定成分を保持。使われ方：長辺の右作用因子と元の評価比較の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の指定右作用比較の前合成は、同じ元の全 Hom 成分の前合成による指定値。 -/
lemma pointedValueMorphismUniversalActionIso_precomp_heq_evaluation
    {K L : KanObject.{u}} (f : K ⟶ L) {C : SSet.{u + 1}}
    (q : C ⟶ vertexFiber pointedSpaceProjection (spaceInfinityVertex K)) :
    HEq ((pointedValueMorphismUniversalActionIso f).precomp q)
      (VertexIso.map (pointedValueHomActionAt f)
        ((pre q).app ((SSet.uliftFunctor.{u + 1, u}).obj L.obj))) := by
  unfold pointedValueMorphismUniversalActionIso
  rw [functorIso_precomp_eq_mapIso]
  exact vertexIsoOfEq_map_heq (pointedValueHomActionAt f) rfl
    (pointedValueHomTransport_morphism_vertex f) ((pre q).app _)

end SerrePositivity.InfinityCategories.F2
