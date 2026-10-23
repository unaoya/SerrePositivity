module

public import SerrePositivity.InfinityCategories.F2.Compact.CoconeLegFiberTransport
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.SpaceEdgeTransportValue

/-!
概要：元の余錐の指定値への fiber 写像は、同じ余錐脚の Kan 値の作用と全自然同型。
方針：元の実 prism による輸送比較を、選択済みの pointed fiber 値比較で共役する。
規約：余錐・脚・fiber 写像と両端の値比較を選び直さない。
使われ方：余極限の点回収から、元の Hom の後合成による恒等射の因子化へ接続。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Compact
variable {B : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}}

/-- 元の指定値に制限した fiber 写像と、同じ余錐脚の Kan 値の作用の全比較。 -/
def coconeLegFiberMap_valueIso (c : JoinCocone F) (b : B _⦋0⦌) :
    FunctorIso (coconeLegFiberMap c b ≫ (pointedSpaceFiberValueEquivalence c.vertex).hom)
      ((pointedSpaceFiberValueEquivalence (F.app (Opposite.op ⦋0⦌) b)).hom ≫
        (SSet.uliftFunctor.{u + 1, u}).map
          (spaceInfinityEdgeValue (coconeTransportLeg c b))) :=
  (coconeLegFiberMap_transportIso c b).postcomp
    (pointedSpaceFiberValueEquivalence c.vertex).hom ≪≫
      (spaceInfinityEdgeTransportValueIso (coconeTransportLeg c b)).symm

/-- 同じ fiber 写像を元の両端の Kan 値へ移した実際の写像。 -/
def coconeLegValueMap (c : JoinCocone F) (b : B _⦋0⦌) :=
  (pointedSpaceFiberValueEquivalence (F.app (Opposite.op ⦋0⦌) b)).inv ≫
    coconeLegFiberMap c b ≫ (pointedSpaceFiberValueEquivalence c.vertex).hom

/-- 元の値比較で移した同じ fiber 写像は、元の指定余錐脚の作用と全自然同型。 -/
def coconeLegValueMap_iso (c : JoinCocone F) (b : B _⦋0⦌) :
    FunctorIso (coconeLegValueMap c b)
      ((SSet.uliftFunctor.{u + 1, u}).map
        (spaceInfinityEdgeValue (coconeTransportLeg c b))) := by
  let q := pointedSpaceFiberValueEquivalence (F.app (Opposite.op ⦋0⦌) b)
  let f := (SSet.uliftFunctor.{u + 1, u}).map
    (spaceInfinityEdgeValue (coconeTransportLeg c b))
  have h := (coconeLegFiberMap_valueIso c b).precomp q.inv
  have k := q.invHomIso.postcomp f
  exact h ≪≫ (by simpa only [Category.assoc, Category.id_comp] using k)

end SerrePositivity.InfinityCategories.F2.Compact
