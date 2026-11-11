module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.BicartesianColimitCocone

/-!
概要：安定な C の Ind の元の任意の押し出し四角形は引き戻しである。
方針：同じ span に構成した bicartesian 全余錐と元の全余錐を関手同型で比較する。
規約：明示交換入力と C の有限全存在を保持し、元の実四角形自身を結論する。
使われ方：I-2 c の零角 fiber/cofiber 判定の一方向。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 元の任意の実押し出し四角形は、Ind 内で同じ実引き戻し四角形である。 -/
lemma ind_pullback_of_pushout_square (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndFiniteLimitExchangeInput.{u})
    {C : SSet.{u}} [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.IsStable C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteLimits C] [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasFiniteColimits C]
    (L : (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ C)
    (hL : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPushoutSquare L) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare L := by
  let e := (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.uliftHornIso.{u, u + 1} 2 0).hom
  let c := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutCocone L).restrict e
  have hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.isColimitCone_iff_restrict_of_isIso _ e).mp hL
  obtain ⟨d, hd, hp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_exists_bicartesianColimitCocone κ hκ hex (e ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pushoutSpan L)
  have ei := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFunctorIsoOfVertexIso d c (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.colimitConeIso d c hd hc)
  let r := _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.uliftSpanSquareReadingIso.{u, u + 1}
  have ht := hp.of_functorIso (ei.precomp r.inv)
  have hv : r.inv ≫ c.val = L := by
    change r.inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap e (𝟙 Δ[0]) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom ≫ L)) = L
    rw [← Category.assoc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap e (𝟙 Δ[0])) _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.spanCoconeSquareIso.hom L]
    change r.inv ≫ (r.hom ≫ L) = L
    exact r.inv_hom_id_assoc L
  rw [hv] at ht
  exact ht

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
