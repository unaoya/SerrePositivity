module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallLimitFunctorContinuity
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.LimitConeFamilyAdjunctionComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.Definition

/-!
概要：μ-small な quasicategory 形状の全極限錐族は、小さい μ-filtered 余極限を頂点へ反映する。
方針：元の全族を同じ濃度で連続な極限関手と全自然同型で比較する。
規約：添字の宇宙 u と値域の宇宙 max u v を分離する。
使われ方：一般の小さい図式の余極限による compact 閉性と引き戻しの生成表示。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：小さい形状の全極限錐族では各脚の μ-filtered 保存が頂点の同じ保存を与える。
方針：同じ μ の極限関手の保存性と、元の全錐族の adjunct 同型を使う。
規約：元の宇宙 u の試験余錐だけで判定し、大きい宇宙の保存性を脚に要求しない。
使われ方：指定した小余極限頂点の native な compact 性。 -/
lemma preservesKappaFilteredColimits_limitFamily_apex_of_small
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {K C : SSet.{max u v}} [Quasicategory K] [Quasicategory C]
    (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall (Cardinal.lift.{v} μ) K)
    (F : (SSet.uliftFunctor.{max u v + 1, max u v}).obj C ⟶
      (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join (Δ[0] : SSet.{max u v + 1})
        ((SSet.uliftFunctor.{max u v + 1, max u v}).obj K))).obj _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{max u v})
    (hF : ∀ x : ((SSet.uliftFunctor.{max u v + 1, max u v}).obj C) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsLimitCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.functorVertexCone (F.app (Opposite.op ⦋0⦌) x)))
    (hleg : ∀ k : ((SSet.uliftFunctor.{max u v + 1, max u v}).obj K) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.{u, v} μ (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr (Δ[0] : SSet.{max u v + 1}) _).app (Opposite.op ⦋0⦌) k))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.PreservesKappaFilteredColimits.{u, v} μ (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt
      (yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl (Δ[0] : SSet.{max u v + 1}) _))) := by
  have : Fact (Cardinal.lift.{v} μ).IsRegular := ⟨(Fact.out : μ.IsRegular).lift⟩
  have hμ' : Cardinal.aleph0 < Cardinal.lift.{v} μ := by
    have h : Cardinal.lift.{v} Cardinal.aleph0 < Cardinal.lift.{v} μ := Cardinal.lift_lt.mpr hμ
    simpa only [Cardinal.lift_aleph0] using h
  obtain ⟨R, ⟨a⟩, hR⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_kappaContinuousSpaceLimitFunctor hμ' K hK
  let Q := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction ((SSet.uliftFunctor.{max u v + 1, max u v}).obj K)
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.SpaceInfinity.{max u v}
  let e := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.limitConeFamily_apexIso_of_constantAdjunction a F hF
  intro J hJ hFiltered D c hc
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered (Cardinal.lift.{v} μ)
      ((SSet.uliftFunctor.{v, u}).obj J) := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaFiltered_ulift J
  let cU := _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.JoinCocone.ulift.{max u v, max u v + 1} c
  have hQ : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone Q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F cU)) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.isColimitCone_of_pointwise
    intro k
    have h := hleg k J D c hc
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _ ?_).mpr h
    change ((cU.val ≫ F) ≫ Q) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt k =
      cU.val ≫ (F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt _)
    simp only [Q, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coneRestriction, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.evaluateFunctorAt_pre]
  have hr := hR ((SSet.uliftFunctor.{v, u}).obj J) _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone Q (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone F cU)) hQ
  have hcore : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone ((F ≫ Q) ≫ R) cU) := by
    apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _ ?_).mpr hr
    simp only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone, Category.assoc]
  exact hcore.of_functorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso.precomp e.symm cU.val)

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.3.4.7" (partial := special) "仮定：正則 κ が非可算、極限形状 K が κ-small な準圏（Lean が強い：任意の κ-small 単体集合形状を扱わない）。結論：各脚が κ-連続な元の全極限錐族の頂点関手も κ-連続（この形状の場合に一致）。各頂点で極限という hF は元の極限の指定であり、結論と別の比較写像を仮定しない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.preservesKappaFilteredColimits_limitFamily_apex_of_small
