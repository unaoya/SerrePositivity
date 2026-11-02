module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.CoherentColimitRawUnitFiberModel

/-!
概要：元の raw fiber 比較を最後辺で輸送した実両端を、消去済み模型式の同じ両端へ揃える。
方針：元の実輸送への分解と元の上面の終点等式を合成する。
規約：比較・輸送・値を保持。使われ方：模型三角形式の残りを同じ raw fiber 比較で表す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable (B : SSet.{u})
  {F G J : (SSet.uliftFunctor.{u + 1, u}).obj B ⟶ SpaceInfinity.{u}}
  (a : SSet.Homotopy F G) (b : SSet.Homotopy G J)
local notation "P" => coherentColimitRawConstantFiberProjection B G
local notation "A" => SSet.yonedaEquiv.symm (coherentColimitRawIntervalVertex B b)
local notation "s" => lift (𝟙 _) (SSet.const (stdSimplex.obj₀Equiv.symm (0 : Fin 1)))
local notation "V" => pointedFiberValueTo (coherentDiagramTotalCocone_vertex J)
local notation "W" => QCatEquivalence.hom
  (pointedSpaceFiberValueEquivalence (coherentDiagramTotalVertex J))
local notation "g₁" => (s ≫ (P ▷ Δ[0]) ≫
  FiberTransportFamily.endpoint (pointedIntervalTransport A)) ≫ V
local notation "f" => Subtype.val (leftUnstraighteningMappingVertexMap F G
  (coherentVertexOfHomotopy a))

/-- 元の raw fiber 比較の輸送後の実始点は、元の下面作用の同じ後合成。 -/
lemma coherentColimitRawUnitFiberTransport_source_map :
    ((coherentColimitRawLowerCompositeAction B a ≫ P) ≫
      coherentColimitFiberTransport B b) ≫ W =
    coherentColimitRawLowerCompositeAction B a ≫ g₁ := by
  have h := congrArg (fun t => coherentColimitRawLowerCompositeAction B a ≫ t)
    (coherentColimitPointValueTo_transport_map B b).symm
  simpa only [Category.assoc] using h

/-- 元の raw fiber 比較の輸送後の実終点は、最後辺の元の模型比較の同じ始点。 -/
lemma coherentColimitRawUnitFiberTransport_target_map :
    ((coherentColimitRawUpperCompositeAction B a ≫ P) ≫
      coherentColimitFiberTransport B b) ≫ W =
    f ≫ (coconeFiberMap (coherentDiagramTotalCocone G) ≫
      coherentColimitFiberTransport B b ≫ W) := by
  have h := congrArg (fun t => coherentColimitRawUpperCompositeAction B a ≫ t)
    (coherentColimitPointValueTo_transport_map B b).symm
  have ht : ((coherentColimitRawUpperCompositeAction B a ≫ P) ≫
      coherentColimitFiberTransport B b) ≫ W =
      coherentColimitRawUpperCompositeAction B a ≫ g₁ := by
    simpa only [Category.assoc] using h
  exact ht.trans (coherentColimitPointValueTo_upper_target_map B a b)

/-- 元の raw fiber 比較の輸送後の値を、同じ二実端点だけで表示変更した指定比較。 -/
def coherentColimitRawUnitFiberTransportValueTo :=
  functorIsoOfEq (((coherentColimitRawUnitFiberComparison B a).postcomp
    (coherentColimitFiberTransport B b)).postcomp W)
    (coherentColimitRawUnitFiberTransport_source_map B a b)
    (coherentColimitRawUnitFiberTransport_target_map B a b)

end SerrePositivity.InfinityCategories.F2
