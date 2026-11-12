module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FilteredPartialPresentation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallPosetColimitCompact

/-!
概要：κ-compact な全図式の指定余極限を、μ-compact な項の μ-filtered 全表示へ移す。
方針：同じ cofinal poset の小さい部分余極限族に、実証済みの compact 閉性を適用する。
規約：元の全余錐の指定頂点を厳密に保持。対象に依存しない小さい生成圏はまだ構成しない。
使われ方：accessible ∞ 圏の濃度変更における各対象の μ-compact 表示。

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

/-- 元の κ-compact な全表示を、同じ指定頂点の μ-compact な μ-filtered 全表示にする。 -/
lemma exists_compactPartialPresentation {κ μ : Cardinal.{u}}
    [Fact κ.IsRegular] [Fact μ.IsRegular] (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ)
    {J : SSet.{u}} [Quasicategory J] [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ J]
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ C)
    {D : (SSet.uliftFunctor.{u + 1, u}).obj J ⟶ C}
    (hD : ∀ j : ((SSet.uliftFunctor.{u + 1, u}).obj J) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ (D.app _ j))
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone D) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) :
    ∃ (K : SSet.{u}) (hK : Quasicategory K),
      letI := hK
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ K ∧
      ∃ G : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C,
        (∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (G.app _ (ULift.up k))) ∧
        ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone G, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d ∧ d.vertex = c.vertex := by
  obtain ⟨I, o, f, hI, _, hf⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.exists_cofinal_kappaFiltered_poset (κ := κ) J
  let := o
  have := hI
  let r := (SSet.uliftFunctor.{u + 1, u}).map f
  have hcI : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (c.restrict r) :=
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isColimitCone_iff_restrict_rightCofinal r (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isRightCofinal_ulift f hf) c).mp hc
  obtain ⟨G, β, hμ, _, hparts, d, hd, hv⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_smallPartialColimitPresentation h hC (c.restrict r) hcI
  refine ⟨nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.SmallFilteredPieces κ μ I), inferInstance, hμ, G, ?_, d, hd, ?_⟩
  · intro k
    obtain ⟨A, rfl⟩ := nerveEquiv.symm.surjective k
    obtain ⟨a, ha, hvertex⟩ := hparts A
    change _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact μ (G.app _ (ULift.up (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex A)))
    rw [← hvertex]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isMuCompact_smallPosetColimit_of_kappaCompact h A.val A.property.2 a ha
    intro j
    exact hD (((SSet.uliftFunctor.{u + 1, u}).map
      (nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.subsetInclusion A.val)) ≫ r).app _ j)
  · exact hv.trans (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_restrict c r)

/-- κ-accessible 圏の各指定対象は、μ-compact な項の小さい μ-filtered 全表示を持つ。 -/
lemma IsKappaAccessible.exists_muCompactPresentation {κ μ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible κ C)
    [Fact μ.IsRegular] (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ) (x : C _⦋0⦌) :
    ∃ (K : SSet.{u}) (hK : Quasicategory K),
      letI := hK
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ K ∧
      ∃ G : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C,
        (∀ k : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (G.app _ (ULift.up k))) ∧
        ∃ d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone G, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone d ∧ d.vertex = x := by
  have : Fact κ.IsRegular := ⟨hC.1⟩
  obtain ⟨A, hA, i, hi⟩ := hC.2.2
  have := hA
  obtain ⟨J, hJ, hκJ, a, c, hv, hc⟩ := hi.presentation x
  have := hJ
  have := hκJ
  have hD : ∀ j : ((SSet.uliftFunctor.{u + 1, u}).obj J) _⦋0⦌,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} κ
        (((SSet.uliftFunctor.{u + 1, u}).map a ≫ i).app _ j) := by
    rintro ⟨j⟩
    exact hi.compact (a.app _ j)
  obtain ⟨K, hK, hμK, G, hG, d, hd, hv'⟩ :=
    exists_compactPartialPresentation h hC.2.1 hD c hc
  exact ⟨K, hK, hμK, G, hG, d, hd, hv'.trans hv⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible export _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessible (exists_muCompactPresentation)


end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
