module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoconeIntervalFiberTransport
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.ConstantDiagramTransportComparisonValue

/-!
概要：元の余錐の区間輸送比較を、同じ定値図式の指定比較の前合成へ値まで戻す。
方針：元の単位の二座標を保ち、始域・終域の表示変更だけを除く。
規約：元の単位と指定比較を保持。使われ方：下側の輸送因子と元の全三角形の照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {B T : SSet.{u + 1}} {F : B ⟶ SpaceInfinity.{u}}
  (c : JoinCocone F) {z : SpaceInfinity.{u} _⦋0⦌}
  (a : T ⟶ intervalMappingSpace c.vertex z)
local notation "S" => coconeIntervalTransportSource c T

/-- 元の余錐の区間比較は、同じ定値図式比較を元の単位の二座標で前合成した値。 -/
lemma coconeIntervalFiberTransportIso_heq_constant :
    HEq (coconeIntervalFiberTransportIso c a)
      ((constantDiagramMappingTransportIso B a).precomp S) := by
  unfold coconeIntervalFiberTransportIso
  exact functorIsoOfEq_heq _ _ _

end SerrePositivity.InfinityCategories.F2
