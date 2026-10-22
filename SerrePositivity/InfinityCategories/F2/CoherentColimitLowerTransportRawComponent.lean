module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitLowerTransportFactor
public import SerrePositivity.InfinityCategories.F2.CoherentColimitRawIntervalTransport
public import SerrePositivity.InfinityCategories.F2.CoconeIntervalHomEndpointTransport

/-!
概要：既存の下側輸送因子を、元の余錐頂点を保持した同じ raw 区間族の比較へ戻す。
方針：元の因子の指定成分と、同じ辺の終点表示だけの移送を合成する。
規約：元の因子・区間・値への比較を保持。使われ方：定値三角形の因子消去との接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 既存の下側輸送因子の値は、同じ元の raw 区間族の同じ Hom 比較の成分の値。 -/
lemma coherentColimitLowerTransportFactorIso_heq_raw_component (B : SSet.{u})
    {F G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
    (H : SSet.Homotopy F G) :
    HEq (coherentColimitLowerTransportFactorIso B H)
      (VertexIso.map ((coconeIntervalFiberHomIso (coherentDiagramTotalCocone F)
        (SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B H))).app
          (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
        ((ihom (leftUnstraightening F)).map
          (pointedSpaceFiberValueEquivalence (coherentDiagramTotalCocone G).vertex).hom)) := by
  refine (coherentColimitLowerTransportFactorIso_heq_component B H).trans ?_
  exact coconeIntervalFiberHomIso_app_value_heq_of_target_eq (coherentDiagramTotalCocone F)
    (coherentDiagramTotalCocone_vertex G).symm _ _
    (coherentColimitRawIntervalFamily_heq_native B H).symm
    (stdSimplex.obj₀Equiv.symm (0 : Fin 1))

end SerrePositivity.InfinityCategories.F2
