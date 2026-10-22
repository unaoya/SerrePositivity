module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitLowerTransportVertices
public import SerrePositivity.InfinityCategories.F2.CoherentColimitLowerTriangleAction
public import SerrePositivity.InfinityCategories.F2.CoherentColimitLowerFiberValue

/-!
概要：下面作用比較から、元の指定区間輸送の比較因子を取り出す。
方針：元の区間族比較の成分を同じ三頂点の等式だけで実射の同型へ移す。
規約：輸送因子を選び直さない。使われ方：上下作用の共役因子の消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}} (H : SSet.Homotopy F G)
local notation "z" => coherentDiagramTotalVertex G
local notation "v" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "m" => CategoryTheory.Functor.map (ihom (leftUnstraightening F))
  (QCatEquivalence.hom (pointedSpaceFiberValueEquivalence z))
local notation "e" => coconeIntervalFiberHomIso (coherentDiagramTotalCocone F)
  (SSet.yonedaEquiv.symm (coherentColimitIntervalVertex B H))

/-- 元の指定区間族比較の同じ成分を、下面の実合成射からの同型として保持する。 -/
def coherentColimitLowerTransportFactorIso : FunctorIso
    (coherentColimitLowerCompositeAction B H)
    (coconeFiberMap (coherentDiagramTotalCocone F) ≫ coherentColimitFiberTransport B H ≫
      (pointedSpaceFiberValueEquivalence z).hom) :=
  vertexIsoOfEq (VertexIso.map (FunctorIso.app e v) m)
    (coherentColimitLowerFactor_middle_vertex B H) (coherentColimitLowerFactor_target_vertex B H)

/-- 指定輸送因子は、元の区間族比較の元の成分の像と同じ指定値を持つ。 -/
lemma coherentColimitLowerTransportFactorIso_heq_component :
    HEq (coherentColimitLowerTransportFactorIso B H)
      (VertexIso.map (FunctorIso.app e v) m) := by
  unfold coherentColimitLowerTransportFactorIso
  exact vertexIsoOfEq_heq _ _ _

/-- 既存の下面作用比較は、同じ元の下面作用比較と指定区間輸送因子の合成。 -/
lemma coherentColimitLowerActionIso_eq_triangle_transport :
    coherentColimitLowerActionIso B H =
      coherentColimitLowerTriangleActionIso B H ≪≫ coherentColimitLowerTransportFactorIso B H := by
  apply eq_of_heq
  refine (coherentColimitLowerActionIso_heq_factors B H).trans ?_
  exact vertexIso_trans_heq_of_heq _ _
    (coherentColimitLowerTriangleActionIso B H) (coherentColimitLowerTransportFactorIso B H)
    (coherentColimitLowerFactor_source_vertex B H)
    (coherentColimitLowerFactor_middle_vertex B H)
    (coherentColimitLowerFactor_target_vertex B H)
    (coherentColimitLowerCompositeIso_map_heq_action B H)
    (coherentColimitLowerTransportFactorIso_heq_component B H).symm

end SerrePositivity.InfinityCategories.F2
