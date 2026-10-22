module

public import SerrePositivity.InfinityCategories.F2.CoconeIntervalFiberTransport

/-!
概要：元の余錐の全区間の Hom 比較を、同じ全輸送比較の curry へ値まで戻す。
方針：元の比較の始点と終点の表示変更だけを除く。
規約：指定値と全係数を保持。使われ方：下側因子への制限を全三角形の輸送と照合する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の全区間の Hom 比較は、同じ選択済み輸送比較を curry した指定値を保持する。 -/
lemma coconeIntervalFiberHomIso_heq_curry {B T : SSet.{u + 1}}
    {F : B ⟶ SpaceInfinity.{u}} (c : JoinCocone F) {z : SpaceInfinity.{u} _⦋0⦌}
    (a : T ⟶ intervalMappingSpace c.vertex z) :
    HEq (coconeIntervalFiberHomIso c a) ((coconeIntervalFiberTransportIso c a).curry) := by
  unfold coconeIntervalFiberHomIso
  have hcast {α β : Sort (u + 2)} (h : α = β) (e : α) : HEq (Eq.mp h e) e := by
    cases h
    rfl
  dsimp only
  refine (hcast _ _).trans ?_
  exact hcast _ _

end SerrePositivity.InfinityCategories.F2
