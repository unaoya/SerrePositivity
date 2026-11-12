module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiberCompactPresentations
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.AccessibleSpanCompactCardinals
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanDiagramColimitTransport

/-!
概要：小余極限保存かつ同値持ち上げを持つ presentable 圏間の射の点 fiber は accessible。
方針：共通 compact 保存濃度を選び、全 compact 成分の小模型へ元の各対象の filtered 全表示を移す。
規約：任意の点射の全小余極限保存や一般 Bousfield 局所化は使わない。
使われ方：固定始域 fiber と局所置換の存在の主経路。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：余完備な accessible 圏間の小余極限保存かつ同値持ち上げ射の点 fiber は accessible。
方針：共通濃度の compact 成分の小模型と、元の対象を頂点とする全生成表示を合わせる。
規約：点射の全小余極限保存を仮定しない。
使われ方：presentable な射の固定標的 fiber の accessibility。 -/
lemma fiber_isAccessible_of_cocomplete_accessible
    {E B : SSet.{u + 1}} [Quasicategory E] [Quasicategory B]
    (hEa : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible E) (hBa : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible B)
    (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits E) (hB : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits B)
    (p : E ⟶ B) (q : (Δ[0] : SSet.{u + 1}) ⟶ B)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p) (hpc : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits p) :
    letI := hp.innerFibration
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible (pullback p q) := by
  have : InnerFibration p := hp.innerFibration
  have hpa : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor p :=
    ⟨Cardinal.aleph0, Cardinal.isRegular_aleph0, hpc.isKappaAccessibleFunctor Cardinal.aleph0⟩
  have hqa : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor q :=
    ⟨Cardinal.aleph0, Cardinal.isRegular_aleph0,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.pointMap_isKappaAccessibleFunctor Cardinal.isRegular_aleph0 q⟩
  obtain ⟨κ, μ, hκ, hμ, hbound, hκμ, he, hd, hb, hpμ, hqμ, hpCompact, hqCompact⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_accessibleSpan_compactCardinal hEa _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.point_isPresentable.isAccessible hBa p q hpa hqa
      Cardinal.aleph0
  have : Fact κ.IsRegular := ⟨hκ⟩
  have : Fact μ.IsRegular := ⟨hμ⟩
  have hq : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (SSet.yonedaEquiv q) := by
    have h := hqCompact (SSet.yonedaEquiv (𝟙 (Δ[0] : SSet.{u + 1})))
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_of_isInitialVertex hbound.le (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.point_vertex_isInitial _))
    rw [← SSet.yonedaEquiv_comp, Category.id_comp] at h
    exact h
  obtain ⟨A, hA, ⟨a⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_smallComponentCompactModel he hd hb p q hp hpCompact hqCompact
  have := hA
  let P := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactVertex μ p q
  let j := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (pullback p q) P).ι
  let i := a.hom ≫ j
  have hf := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.pullback_fst_isKappaAccessibleFunctor p q hp he.hasSmallKappaFilteredColimits
    hd.hasSmallKappaFilteredColimits hpμ hqμ
  have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.pullback_snd_isKappaAccessibleFunctor p q hp he.hasSmallKappaFilteredColimits
    hd.hasSmallKappaFilteredColimits hpμ hqμ
  have hi : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaCompactGenerating μ i := by
    refine ⟨a.isQCatEquivalence.isFullyFaithful.comp
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _), ?_, ?_⟩
    · intro v
      exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.componentCompactObjects_vertex_isKappaCompact μ p q hκμ hf hs hpμ hpCompact
        (a.hom.app (Opposite.op ⦋0⦌) (ULift.up v))
    · intro x
      obtain ⟨M, hM, hfiltered, D, hD, c, hc, hv⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_componentCompactFiberPresentation
        hbound hE hB he hb p q hp hpc hpCompact hq x
      have := hM
      have := hfiltered
      let H := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift P D hD
      let b := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown (H ≫ a.inv)
      have hbb : (SSet.uliftFunctor.{u + 1, u}).map b = H ≫ a.inv := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown_lift _
      have heq : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((SSet.uliftFunctor.{u + 1, u}).map b ≫ i) D := by
        rw [hbb]
        dsimp only [i]
        simpa only [Category.assoc, Category.id_comp, H, j, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι] using
          (a.invHomIso.precomp H).postcomp j
      obtain ⟨c', hc', hv'⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.exists_colimitCocone_functorIso_sameVertex heq.symm c hc
      exact ⟨M, hM, hfiltered, b, c', hv'.trans hv, hc'⟩
  exact ⟨μ, hμ, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.fiber_hasSmallKappaFilteredColimits hμ p q hp
    he.hasSmallKappaFilteredColimits hpμ, A, hA, i, hi⟩

/-- 概要：presentable 圏間の小余極限保存かつ同値持ち上げ射の任意の点 fiber は accessible。
方針：余完備な accessible 圏の点 fiber の全生成構成を適用する。
規約：第二脚には任意の点射を許し、全小余極限保存は要求しない。
使われ方：固定始域 fiber の局所置換と e5 の公開入口。 -/
lemma fiber_isAccessible_of_presentable
    {E B : SSet.{u + 1}} [Quasicategory E] [Quasicategory B]
    (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) (hB : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable B)
    (p : E ⟶ B) (q : (Δ[0] : SSet.{u + 1}) ⟶ B)
    (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p) (hpc : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits p) :
    letI := hp.innerFibration
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible (pullback p q) :=
  fiber_isAccessible_of_cocomplete_accessible hE.isAccessible hB.isAccessible
    hE.hasSmallColimits hB.hasSmallColimits p q hp hpc

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
