module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitRightTailNativeFactorization

/-!
概要：元の残り二因子と上側単位を、同じ一点輸送・二面比較・a6 模型比較へ戻す。
方針：元の指定自然性と模型単位の交換式を同じ実中間頂点で合成する。
規約：最後辺の模型比較を再選択しない。使われ方：模型五因子式の外側単位消去。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u}) [Quasicategory B]
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  (a : SSet.Homotopy F G) (b : SSet.Homotopy G J)
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex J)
local notation "f" => Subtype.val (leftUnstraighteningMappingVertexMap F G
  (coherentVertexOfHomotopy a))
local notation "P" => constantUnstraighteningFiberProjection
  (CategoryTheory.Functor.obj SSet.uliftFunctor B)
  (JoinCocone.vertex (coherentDiagramTotalCocone G))
local notation "A" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B b)
local notation "s" => lift (𝟙 _) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
local notation "g₁" => (s ≫ (P ▷ Δ[0]) ≫
  FiberTransportFamily.endpoint (pointedIntervalTransport A)) ≫ V

omit [Quasicategory B] in
/-- 元の一点輸送と元の raw 二面比較を同じ固定値で合成した残りの指定比較。 -/
def coherentColimitRightTailTransportValueTo :=
  (coherentColimitConstantPointValueToIso B b).precomp
    (coherentColimitRawLowerCompositeAction B a) ≪≫
  functorIsoOfEq ((coherentColimitRawUnitActionComparison B a).postcomp g₁)
    rfl (coherentColimitPointValueTo_upper_target_map B a b)

/-- 元の残り二因子と上側単位は、同じ輸送比較と元の最後辺の模型比較へ消去される。 -/
lemma coherentColimitRightTail_valueTo_unit_cancel :
    vertexIsoOfEq (coherentColimitUnitRightTailValueTo B (a := a) (b := b))
      (coherentColimitFirstPost_valueTo_source_vertex B a b)
      (coherentColimitValueProjection_composite_vertex B a b) ≪≫
      (coherentColimitUpperUnitFactorIso B b).precomp f =
    coherentColimitRightTailTransportValueTo B a b ≪≫
      (coherentColimitIntervalModelUnitComparison B b).precomp f := by
  rw [coherentColimitRightTail_valueTo_eq_native, Iso.trans_assoc,
    coherentColimitIntervalModelUnitComparison_precomp_exchange,
    ← Iso.trans_assoc, coherentColimitFirstPost_lower_exchange]
  rfl

end SerrePositivity.InfinityCategories.F2
