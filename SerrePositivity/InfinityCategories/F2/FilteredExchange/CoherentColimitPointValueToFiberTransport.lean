module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.PointedIntervalTransportPoint
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoherentColimitFirstPostLowerExchange
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorIsoTriplePostTransport

/-!
概要：残る raw 二面比較の後合成を、同じ最後辺の元の実 fiber 輸送へ分解する。
方針：元の区間族の同じ指定点の実制限と、raw/native 終点表示の等式を使う。
規約：最後辺の輸送を再選択しない。使われ方：最初辺の元の模型比較への照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
/-- 元の底と元の余錐頂点を明示した raw 定値全空間の同じ fiber 射影。 -/
def coherentColimitRawConstantFiberProjection (B : SSet.{u})
    (G : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}) :=
  constantUnstraighteningFiberProjection ((SSet.uliftFunctor.{u + 1, u}).obj B)
    (JoinCocone.vertex (coherentDiagramTotalCocone G))

variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  (a : SSet.Homotopy F G) (b : SSet.Homotopy G J)
local notation "P" => coherentColimitRawConstantFiberProjection B G
local notation "A" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B b)
local notation "A'" => SSet.yonedaEquiv.symm (coherentColimitIntervalVertex B b)
local notation "l" => stdSimplex.obj₀Equiv.symm (0 : Fin 1)
local notation "s" => lift (𝟙 _) (SSet.const l)
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex J)
local notation "W" => QCatEquivalence.hom
  (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex J))
local notation "g₁" => (s ≫ (P ▷ Δ[0]) ≫
  FiberTransportFamily.endpoint (pointedIntervalTransport A)) ≫ V

omit a in
/-- 残る後合成の実射は、同じ最後辺の元の実 fiber 輸送と同じ値射影の合成。 -/
lemma coherentColimitPointValueTo_transport_map :
    g₁ = P ≫ coherentColimitFiberTransport B b ≫ W := by
  rw [pointedIntervalTransportAt_pre, Category.assoc]
  exact congrArg (fun t => P ≫ t)
    (pointedIntervalTransportAt_valueTo_eq (coherentDiagramTotalCocone_vertex J) A A'
      (coherentColimitRawIntervalFamily_heq_native B b) l)

omit b in
/-- 元の raw 二面比較を、同じ元の標的余錐の pointed fiber へ写した指定比較。 -/
def coherentColimitRawUnitFiberComparison :=
  (coherentColimitRawUnitActionComparison B a).postcomp
    (coherentColimitRawConstantFiberProjection B G)

/-- 残る二面比較の像は、同じ raw fiber 比較の元の最後辺輸送と値への二段の後合成。 -/
lemma coherentColimitRawUnitAction_transport_heq_fiber :
    HEq ((coherentColimitRawUnitActionComparison B a).postcomp g₁)
      (((coherentColimitRawUnitFiberComparison B a).postcomp
        (coherentColimitFiberTransport B b)).postcomp W) := by
  exact functorIso_postcomp_triple_transport_heq
    (coherentColimitRawUnitActionComparison B a) P (coherentColimitFiberTransport B b) W g₁
    (coherentColimitPointValueTo_transport_map B b)

end SerrePositivity.InfinityCategories.F2
