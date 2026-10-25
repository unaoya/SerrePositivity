module

public import SerrePositivity.InfinityCategories.F2.Presentable.SmallLimitFunctorContinuity
public import SerrePositivity.InfinityCategories.F2.Presentable.LimitConeFamilyAdjunctionComparison
public import SerrePositivity.InfinityCategories.F2.Compact.Definition

/-!
概要：μ-small な quasicategory 形状の全極限錐族は、小さい μ-filtered 余極限を頂点へ反映する。
方針：元の全族を同じ濃度で連続な極限関手と全自然同型で比較する。
規約：添字の宇宙 u と値域の宇宙 max u v を分離する。
使われ方：一般の小さい図式の余極限による compact 閉性と引き戻しの生成表示。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：小さい形状の全極限錐族では各脚の μ-filtered 保存が頂点の同じ保存を与える。
方針：同じ μ の極限関手の保存性と、元の全錐族の adjunct 同型を使う。
規約：元の宇宙 u の試験余錐だけで判定し、大きい宇宙の保存性を脚に要求しない。
使われ方：指定した小余極限頂点の native な compact 性。 -/
lemma preservesKappaFilteredColimits_limitFamily_apex_of_small
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {K C : SSet.{max u v}} [Quasicategory K] [Quasicategory C]
    (hK : IsKappaSmall (Cardinal.lift.{v} μ) K)
    (F : (SSet.uliftFunctor.{max u v + 1, max u v}).obj C ⟶
      (ihom (join (Δ[0] : SSet.{max u v + 1})
        ((SSet.uliftFunctor.{max u v + 1, max u v}).obj K))).obj SpaceInfinity.{max u v})
    (hF : ∀ x : ((SSet.uliftFunctor.{max u v + 1, max u v}).obj C) _⦋0⦌,
      IsLimitCone (functorVertexCone (F.app (Opposite.op ⦋0⦌) x)))
    (hleg : ∀ k : ((SSet.uliftFunctor.{max u v + 1, max u v}).obj K) _⦋0⦌,
      Compact.PreservesKappaFilteredColimits.{u, v} μ (F ≫ evaluateFunctorAt
        ((joinInr (Δ[0] : SSet.{max u v + 1}) _).app (Opposite.op ⦋0⦌) k))) :
    Compact.PreservesKappaFilteredColimits.{u, v} μ (F ≫ evaluateFunctorAt
      (yonedaEquiv (joinInl (Δ[0] : SSet.{max u v + 1}) _))) := by
  have : Fact (Cardinal.lift.{v} μ).IsRegular := ⟨(Fact.out : μ.IsRegular).lift⟩
  have hμ' : Cardinal.aleph0 < Cardinal.lift.{v} μ := by
    have h : Cardinal.lift.{v} Cardinal.aleph0 < Cardinal.lift.{v} μ := Cardinal.lift_lt.mpr hμ
    simpa only [Cardinal.lift_aleph0] using h
  obtain ⟨R, ⟨a⟩, hR⟩ := exists_kappaContinuousSpaceLimitFunctor hμ' K hK
  let Q := coneRestriction ((SSet.uliftFunctor.{max u v + 1, max u v}).obj K)
    SpaceInfinity.{max u v}
  let e := limitConeFamily_apexIso_of_constantAdjunction a F hF
  intro J hJ hFiltered D c hc
  have : IsKappaFiltered (Cardinal.lift.{v} μ)
      ((SSet.uliftFunctor.{v, u}).obj J) := isKappaFiltered_ulift J
  let cU := JoinCocone.ulift.{max u v, max u v + 1} c
  have hQ : IsColimitCone (mapJoinCocone Q (mapJoinCocone F cU)) := by
    apply isColimitCone_of_pointwise
    intro k
    have h := hleg k J D c hc
    apply (isColimitCone_iff_of_cocone_val_eq _ _ ?_).mpr h
    change ((cU.val ≫ F) ≫ Q) ≫ evaluateFunctorAt k =
      cU.val ≫ (F ≫ evaluateFunctorAt _)
    simp only [Q, coneRestriction, Category.assoc, evaluateFunctorAt_pre]
  have hr := hR ((SSet.uliftFunctor.{v, u}).obj J) _
    (mapJoinCocone Q (mapJoinCocone F cU)) hQ
  have hcore : IsColimitCone (mapJoinCocone ((F ≫ Q) ≫ R) cU) := by
    apply (isColimitCone_iff_of_cocone_val_eq _ _ ?_).mpr hr
    simp only [mapJoinCocone, Category.assoc]
  exact hcore.of_functorIso (FunctorIso.precomp e.symm cU.val)

end SerrePositivity.InfinityCategories.F2.Presentable
