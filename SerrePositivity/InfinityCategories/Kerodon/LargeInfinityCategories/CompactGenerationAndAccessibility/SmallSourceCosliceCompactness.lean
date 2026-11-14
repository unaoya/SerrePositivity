module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.ColimitSourceCosliceComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.FullCompactFactorization
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ConeTerminalSliceComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.ColimitCosliceRestriction

/-!
概要：小さい compact 前置図式の余錐の頂点は、その全 coslice 内でも compact。
方針：前置図式の余極限を一度付け加え、二つの自明 Kan 制限で一点 coslice と比較する。
規約：本葉の周囲の圏だけに前置図式の余極限を要求する。
使われ方：前層内で極限前置図式全体を固定する相対因子化。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：前置図式の余極限と余錐頂点が compact なら、元の全余錐も compact。
方針：余極限余錐全体からの二つの制限を通じて一点 coslice の compact 性を移す。
規約：前置図式に終対象は要求しない。
使われ方：極限段を含む全前置図式を固定する compact 因子化。 -/
lemma isKappaCompact_cosliceVertex_of_compactColimit
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {K C : SSet.{u + 1}} [Quasicategory K] [Quasicategory C]
    {q : K ⟶ C} (cq : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) (hcq : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone cq)
    (hcompact : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ cq.vertex)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ c.vertex) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (C := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder q) c := by
  obtain ⟨H, hH, hHp⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_colimitSourceCosliceComparison cq hcq
  have hv : (show _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K Δ[0] ≫ cq.val) from
      H.app (Opposite.op ⦋0⦌) c).vertex = c.vertex :=
    congrArg (fun f ↦ f.app (Opposite.op ⦋0⦌) c) hHp
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (H.app (Opposite.op ⦋0⦌) c) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_pointCosliceVertex hμ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K Δ[0] ≫ cq.val)
    · exact hcompact
    · rw [hv]
      exact hc
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isKappaCompact_of_fullyFaithful_image H hH.isFullyFaithful
    (_root_.SerrePositivity.InfinityCategories.HTT.AccessibleInfinityCategories.equivalence_preservesSmallKappaFilteredColimits μ hH) c ht

/-- 概要：余完備な周囲では、小さい compact 全前置図式の compact 頂点余錐は compact。
方針：前置図式の余極限の compact 性と二つの制限の比較を使う。
規約：前置図式に終頂点や有限性を要求しない。
使われ方：一般 accessible 圏の Ind 模型を前層内で相対因子化する準備。 -/
lemma isKappaCompact_smallSourceCosliceVertex
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {A : SSet.{u}} [Quasicategory A] (hA : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ A)
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits C)
    (q : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ C)
    (hq : ∀ a, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (q.app _ a))
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ c.vertex) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (C := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder q) c := by
  obtain ⟨cq, hcq⟩ := hC A q
  exact isKappaCompact_cosliceVertex_of_compactColimit hμ cq hcq
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.isKappaCompact_smallQuasicategoryColimit_universe hμ A hA cq hcq hq) c hc

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "5.4.5.13" (partial := stronger-hyp) "仮定：非可算正則 κ、κ-small な準圏形状と全頂点が κ-compact な図式・κ-compact な余錐頂点（Lean が強い：周囲 C は全小余完備、形状は準圏）。結論：同じ全余錐自身が Cp/ の κ-compact 対象（この場合に一致）。頂点だけの compact 性に弱めていない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.isKappaCompact_smallSourceCosliceVertex
