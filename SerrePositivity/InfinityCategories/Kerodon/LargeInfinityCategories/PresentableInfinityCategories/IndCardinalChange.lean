module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallFamilyGeneratorTransport
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallGeneratorPresentation
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.AccessibleEquivalence
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：実証済みの濃度条件から、Ind 圏と任意の accessible ∞ 圏の μ-accessibility を得る。
方針：共通の μ-compact 族の小さい全部分模型へ全表示を移し、Ind 表現の同値で輸送する。
規約：κ ≤ μ だけの単調性は主張しない。κ・μ の正則性と冪の評価を保持する。
使われ方：HTT 5.4.2 の濃度変更と、小さい濃度族に共通の accessibility。

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

/-- 元の Indκ の、実証済みの μ-compact 生成圏による μ-accessibility。 -/
lemma indInfinity_isMuAccessible {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ) (A : SSet.{u}) [Quasicategory A] :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A) := by
  let hC := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ind_hasSmallKappaFilteredColimits κ A
  let i := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda κ A
  let v : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.SmallPosetDiagramCode κ μ A → (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.IndInfinity κ A) _⦋0⦌ :=
    fun q ↦ q.vertex hC i
  let hX := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.ind_hasSmallFixedVertexMaps κ A
  have hi := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda_isKappaCompactGenerating κ A
  have hg : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaCompactGenerating μ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFullModelInclusion hX v) := by
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFullModelInclusion_isKappaCompactGenerating hX v
    · intro q
      exact q.vertex_isMuCompact h hC i hi.compact
    · intro x
      exact hi.exists_smallFamilyPresentation h hC x
  refine ⟨Fact.out, ?_, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFullModel hX v, inferInstance,
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.smallFullModelInclusion hX v, hg⟩
  intro K hK hμK D
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered κ K := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.isKappaFiltered_of_le h.le
  exact hC K D

/-- 任意の元の κ-accessible ∞ 圏は、同じ明示的な濃度条件の下で μ-accessible。 -/
lemma IsKappaAccessible.of_cardinalChangeBound {κ μ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible κ C)
    [Fact μ.IsRegular] (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ C := by
  have : Fact κ.IsRegular := ⟨hC.1⟩
  obtain ⟨A, hA, ⟨e⟩⟩ := hC.exists_indEquivalence
  have := hA
  exact (indInfinity_isMuAccessible h A).of_equivalence e

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible export _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessible (of_cardinalChangeBound)


/-- 同じ宇宙の任意の上限を超える濃度で、元の圏は accessibility を持つ。 -/
lemma IsKappaAccessible.exists_larger {κ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible κ C)
    (σ : Cardinal.{u}) :
    ∃ μ : Cardinal.{u}, σ < μ ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ C := by
  obtain ⟨μ, hμ, hσ, h⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_regular_cardinalChangeBound κ σ
  have : Fact μ.IsRegular := ⟨hμ⟩
  exact ⟨μ, hσ, hC.of_cardinalChangeBound h⟩

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible export _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessible (exists_larger)


/-- accessibility は、同じ宇宙の任意の上限より大きい正則濃度で実現できる。 -/
@[kerodon 06KM]
lemma IsAccessible.exists_larger {C : SSet.{u + 1}} [Quasicategory C]
    (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible C) (σ : Cardinal.{u}) :
    ∃ μ : Cardinal.{u}, σ < μ ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ C := by
  obtain ⟨κ, hκ⟩ := hC
  exact hκ.exists_larger σ

with_weak_namespace _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible export _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsAccessible (exists_larger)


/-- 小さい accessible 圏の族は、任意の上限を超える一つの同じ正則濃度で accessible。 -/
@[kerodon 06KP]
lemma exists_common_accessibilityCardinal {ι : Type u} (C : ι → SSet.{u + 1})
    [∀ i, Quasicategory (C i)] (hC : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible (C i)) (σ : Cardinal.{u}) :
    ∃ μ : Cardinal.{u}, μ.IsRegular ∧ σ < μ ∧ ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ (C i) := by
  let κ : ι → Cardinal.{u} := fun i ↦ (hC i).choose
  have hκ (i : ι) : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible (κ i) (C i) := (hC i).choose_spec
  obtain ⟨μ, hμ, hσ, h⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_regular_cardinalChangeBound_family κ σ
  have : Fact μ.IsRegular := ⟨hμ⟩
  exact ⟨μ, hμ, hσ, fun i ↦ (hκ i).of_cardinalChangeBound (h i)⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HA "5.3.2.12" (partial := component) "仮定：presentable な準圏 C の accessibility（HA の仮定から従う）。結論：σ=ℵ₀ を指定すると、ある非可算正則 μ に関して C は μ-compact 生成となる（(1) の存在部分に一致）。同じ μ における tensor・単位と全代数の加群の compact 条件 (2)〜(4) は含まれない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsAccessible.exists_larger
attribute [cite HTT "5.3.5.12"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessible.of_cardinalChangeBound
attribute [cite HTT "5.4.2.9"] _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsKappaAccessible.of_cardinalChangeBound
