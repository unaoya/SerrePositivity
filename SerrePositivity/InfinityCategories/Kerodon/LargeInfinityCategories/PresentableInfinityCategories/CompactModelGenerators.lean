module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallCompactModels
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleIndRepresentation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.KanDiagramColimitTransport

/-!
概要：全 compact 対象の任意の小さい全同値模型は、同じ濃度の compact 生成圏となる。
方針：元の生成表示を全部分圏へ持ち上げ、模型同値の逆で全図式を戻す。
規約：各対象の指定頂点と全余錐を保持する。
使われ方：compact 始域 comma の標準余錐の密度比較。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories


/-- 概要：全 μ-compact 全部分圏の小模型の包含は μ-compact 生成関手となる。
方針：元の各 filtered 表示を同値の逆で小模型へ移し、全関手同型で余極限を戻す。
規約：元の圏の固定頂点写像の厳密な小ささは不要。
使われ方：全 compact 模型からの Ind 比較と標準密度余錐。 -/
lemma IsKappaAccessible.compactModel_isKappaCompactGenerating
    {μ : Cardinal.{u}} {C : SSet.{u + 1}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ C) {A : SSet.{u}} [Quasicategory A]
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj A)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{u, u + 1} μ C)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaCompactGenerating μ (e.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion.{u, u + 1} μ C) := by
  let j := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion.{u, u + 1} μ C
  refine ⟨e.isQCatEquivalence.isFullyFaithful.comp
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion_isFullyFaithful μ C), ?_, ?_⟩
  · intro a
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (e.hom.app (Opposite.op ⦋0⦌) (ULift.up a))
  · intro x
    obtain ⟨B, hB, i, hi⟩ := hC.2.2
    have := hB
    obtain ⟨I, hI, hfiltered, d, c, hv, hc⟩ := hi.presentation x
    have := hI
    have := hfiltered
    let D := (SSet.uliftFunctor.{u + 1, u}).map d ≫ i
    let H := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ) D (by
      rintro ⟨k⟩
      exact hi.compact (d.app (Opposite.op ⦋0⦌) k))
    let a := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown (H ≫ e.inv)
    have ha : (SSet.uliftFunctor.{u + 1, u}).map a = H ≫ e.inv := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown_lift _
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((SSet.uliftFunctor.{u + 1, u}).map a ≫ (e.hom ≫ j)) D := by
      rw [ha, Category.assoc]
      simpa only [Category.assoc, Category.id_comp, H, j, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion,
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι] using (e.invHomIso.precomp H).postcomp j
    obtain ⟨c', hc', hv'⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.exists_colimitCocone_functorIso_sameVertex he.symm c hc
    exact ⟨I, hI, hfiltered, a, c', hv'.trans hv, hc'⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible export _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessible (compactModel_isKappaCompactGenerating)


/-- 概要：指定した全 compact 小模型から、元の圏への全 Ind 同値を構成する。
方針：同じ模型の生成性を実証済み Ind 比較の同値判定へ渡す。
規約：全 compact 模型と元の包含を全関手同型で回収する。
使われ方：標準 compact comma の全密度余錐の構成。 -/
lemma IsKappaAccessible.exists_compactModelIndRepresentation
    {μ : Cardinal.{u}} {C : SSet.{u + 1}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ C) {A : SSet.{u}} [Quasicategory A]
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence ((SSet.uliftFunctor.{u + 1, u}).obj A)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactObjects.{u, u + 1} μ C)) :
    ∃ g : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity μ A) C,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ g.hom ∧ Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda μ A ≫ g.hom)
        (e.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion.{u, u + 1} μ C)) := by
  have : Fact μ.IsRegular := ⟨hC.1⟩
  have hi := hC.compactModel_isKappaCompactGenerating e
  obtain ⟨G, hG, ⟨β⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.exists_indComparison hC.2.1
    (e.hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.kappaCompactInclusion.{u, u + 1} μ C)
  exact ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indComparisonEquivalence hi hG β, hG, ⟨β⟩⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible export _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessible (exists_compactModelIndRepresentation)


end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.3.5.12"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessible.compactModel_isKappaCompactGenerating
attribute [cite HTT "5.4.2.13" (partial := stronger-hyp) "仮定：accessible な二準圏と accessible 関手（Lean が強い：始域の固定頂点全写像が宇宙小である strict 条件を要求）。結論：ある大きい正則濃度 μ で関手が μ-compact 対象を保ち、全 compact 小模型からの制限が元の関手を同値を除き決める（この場合に一致）。一般の始域への strict 模型輸送をここでは追加していない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessible.exists_compactModelIndRepresentation
attribute [cite HTT "5.4.2.2"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessible.compactModel_isKappaCompactGenerating
