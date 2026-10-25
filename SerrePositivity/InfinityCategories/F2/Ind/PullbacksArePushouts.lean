module

public import SerrePositivity.InfinityCategories.F2.Ind.BicartesianLimitCone

/-!
概要：安定な C の Ind の元の任意の引き戻し四角形は押し出しである。
方針：同じ cospan に構成した bicartesian 全錐と元の全錐を関手同型で比較する。
規約：明示交換入力と C の有限極限存在を保持し、元の実四角形自身を結論する。
使われ方：I-2 c の零角 fiber/cofiber 判定の一方向。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 元の任意の実引き戻し四角形は、Ind 内で同じ実押し出し四角形である。 -/
lemma ind_pushout_of_pullback_square (κ : Cardinal.{u}) [Fact κ.IsRegular]
    (hκ : Cardinal.aleph0 ≤ κ) (hex : IndFiniteLimitExchangeInput.{u})
    {C : SSet.{u}} [Quasicategory C] [IsStable C] [HasFiniteLimits C]
    (L : (Δ[1] : SSet.{u + 1}) ⊗ Δ[1] ⟶ IndInfinity κ C)
    (hL : IsPullbackSquare L) : IsPushoutSquare L := by
  let e := (uliftHornIso.{u, u + 1} 2 2).hom
  let c := restrictJoinCone (pullbackCone L) e
  have hc : IsLimitCone c := (isLimitCone_restrict_iff_of_isIso _ e).mpr hL
  obtain ⟨d, hd, hp⟩ := ind_exists_bicartesianLimitCone κ hκ hex (e ≫ pullbackCospan L)
  have ei := coneFunctorIsoOfVertexIso d c (limitConeIso d c hd hc)
  let r := uliftCospanSquareReadingIso.{u, u + 1}
  have ht := hp.of_functorIso (ei.precomp r.inv)
  have hv : r.inv ≫ c.val = L := by
    change r.inv ≫ (joinMap (𝟙 Δ[0]) e ≫ (cospanConeSquareIso.hom ≫ L)) = L
    rw [← Category.assoc (joinMap (𝟙 Δ[0]) e) cospanConeSquareIso.hom L]
    change r.inv ≫ (r.hom ≫ L) = L
    exact r.inv_hom_id_assoc L
  rw [hv] at ht
  exact ht

end SerrePositivity.InfinityCategories.F2.Ind
