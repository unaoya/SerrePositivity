module

public import SerrePositivity.InfinityCategories.F2.CoherentColimitRawUnitFiberTransportEndpoints
public import SerrePositivity.InfinityCategories.F2.CoherentColimitRawTransportPointPrism
public import SerrePositivity.InfinityCategories.F2.FunctorIsoPostPairTransport

/-!
概要：元の二面比較の最後辺輸送を、同じ raw 輸送と同じ値射の像として保持する。
方針：raw/native 輸送の実合成射の等式を、元の指定同型と実両端へ適用する。
規約：二面比較・最後辺輸送・値を保持。使われ方：逆第一辺因子との合成の反映。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  (a : SSet.Homotopy F G) (b : SSet.Homotopy G J)
local notation "e" => coherentColimitRawUnitFiberComparison B a
local notation "t" => coherentColimitRawFiberTransport B b
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex J)
local notation "W" => QCatEquivalence.hom
  (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex J))

/-- 元の二面輸送の指定値は、同じ raw 最後辺輸送と同じ値射の像。 -/
lemma coherentColimitRawUnitFiberTransportValueTo_heq_raw :
    HEq (coherentColimitRawUnitFiberTransportValueTo B a b)
      ((FunctorIso.postcomp e t).postcomp V) := by
  have hn := functorIsoOfEq_heq
    (((coherentColimitRawUnitFiberComparison B a).postcomp
      (coherentColimitFiberTransport B b)).postcomp W)
    (coherentColimitRawUnitFiberTransport_source_map B a b)
    (coherentColimitRawUnitFiberTransport_target_map B a b)
  exact hn.trans (functorIso_postcomp_pair_heq_of_pair_eq e
    (coherentColimitFiberTransport B b) W t V
    (coherentColimitRawFiberTransport_valueTo B b).symm)

/-- 同じ raw 二面輸送の実始点を、元の模型式で使う同じ実始点へ戻す。 -/
lemma coherentColimitRawUnitFiberTransport_raw_source_map :
    ((coherentColimitRawLowerCompositeAction B a ≫
      coherentColimitRawConstantFiberProjection B G) ≫ t) ≫ V =
    coherentColimitRawLowerCompositeAction B a ≫
      ((CartesianMonoidalCategory.lift (𝟙 _) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1))) ≫
        (coherentColimitRawConstantFiberProjection B G ▷ Δ[0]) ≫
          (pointedIntervalTransport
            (SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B b))).endpoint) ≫ V) := by
  exact (postcomp_pair_eq_of_pair_eq
    (coherentColimitRawLowerCompositeAction B a ≫ coherentColimitRawConstantFiberProjection B G)
    t V (coherentColimitFiberTransport B b) W
    (coherentColimitRawFiberTransport_valueTo B b)).trans
    (coherentColimitRawUnitFiberTransport_source_map B a b)

/-- 同じ raw 二面輸送の実終点を、元の最後辺模型比較の同じ実始点へ戻す。 -/
lemma coherentColimitRawUnitFiberTransport_raw_target_map :
    ((coherentColimitRawUpperCompositeAction B a ≫
      coherentColimitRawConstantFiberProjection B G) ≫ t) ≫ V =
    (leftUnstraighteningMappingVertexMap F G (coherentVertexOfHomotopy a)).val ≫
      (coconeFiberMap (coherentDiagramTotalCocone G) ≫ coherentColimitFiberTransport B b ≫ W) := by
  exact (postcomp_pair_eq_of_pair_eq
    (coherentColimitRawUpperCompositeAction B a ≫ coherentColimitRawConstantFiberProjection B G)
    t V (coherentColimitFiberTransport B b) W
    (coherentColimitRawFiberTransport_valueTo B b)).trans
    (coherentColimitRawUnitFiberTransport_target_map B a b)

end SerrePositivity.InfinityCategories.F2
