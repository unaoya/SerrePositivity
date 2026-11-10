module

public import SerrePositivity.InfinityCategories.F2.Presentable.SmallFamilyGeneratorTransport
public import SerrePositivity.InfinityCategories.F2.Presentable.SmallGeneratorPresentation
public import SerrePositivity.InfinityCategories.F2.Presentable.AccessibleEquivalence
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：実証済みの濃度条件から、Ind 圏と任意の accessible ∞ 圏の μ-accessibility を得る。
方針：共通の μ-compact 族の小さい全部分模型へ全表示を移し、Ind 表現の同値で輸送する。
規約：κ ≤ μ だけの単調性は主張しない。κ・μ の正則性と冪の評価を保持する。
使われ方：HTT 5.4.2 の濃度変更と、小さい濃度族に共通の accessibility。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 元の Indκ の、実証済みの μ-compact 生成圏による μ-accessibility。 -/
lemma indInfinity_isMuAccessible {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : IsCardinalChangeBound κ μ) (A : SSet.{u}) [Quasicategory A] :
    IsKappaAccessible μ (Ind.IndInfinity κ A) := by
  let hC := Ind.ind_hasSmallKappaFilteredColimits κ A
  let i := Ind.indYoneda κ A
  let v : SmallPosetDiagramCode κ μ A → (Ind.IndInfinity κ A) _⦋0⦌ :=
    fun q ↦ q.vertex hC i
  let hX := Ind.ind_hasSmallFixedVertexMaps κ A
  have hi := indYoneda_isKappaCompactGenerating κ A
  have hg : IsKappaCompactGenerating μ (smallFullModelInclusion hX v) := by
    apply smallFullModelInclusion_isKappaCompactGenerating hX v
    · intro q
      exact q.vertex_isMuCompact h hC i hi.compact
    · intro x
      exact hi.exists_smallFamilyPresentation h hC x
  refine ⟨Fact.out, ?_, smallFullModel hX v, inferInstance,
    smallFullModelInclusion hX v, hg⟩
  intro K hK hμK D
  have : IsKappaFiltered κ K := isKappaFiltered_of_le h.le
  exact hC K D

/-- 任意の元の κ-accessible ∞ 圏は、同じ明示的な濃度条件の下で μ-accessible。 -/
lemma IsKappaAccessible.of_cardinalChangeBound {κ μ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] (hC : IsKappaAccessible κ C)
    [Fact μ.IsRegular] (h : IsCardinalChangeBound κ μ) : IsKappaAccessible μ C := by
  have : Fact κ.IsRegular := ⟨hC.1⟩
  obtain ⟨A, hA, ⟨e⟩⟩ := hC.exists_indEquivalence
  have := hA
  exact (indInfinity_isMuAccessible h A).of_equivalence e

/-- 同じ宇宙の任意の上限を超える濃度で、元の圏は accessibility を持つ。 -/
lemma IsKappaAccessible.exists_larger {κ : Cardinal.{u}}
    {C : SSet.{u + 1}} [Quasicategory C] (hC : IsKappaAccessible κ C)
    (σ : Cardinal.{u}) :
    ∃ μ : Cardinal.{u}, σ < μ ∧ IsKappaAccessible μ C := by
  obtain ⟨μ, hμ, hσ, h⟩ := exists_regular_cardinalChangeBound κ σ
  have : Fact μ.IsRegular := ⟨hμ⟩
  exact ⟨μ, hσ, hC.of_cardinalChangeBound h⟩

/-- accessibility は、同じ宇宙の任意の上限より大きい正則濃度で実現できる。 -/
@[kerodon 06KM]
lemma IsAccessible.exists_larger {C : SSet.{u + 1}} [Quasicategory C]
    (hC : IsAccessible C) (σ : Cardinal.{u}) :
    ∃ μ : Cardinal.{u}, σ < μ ∧ IsKappaAccessible μ C := by
  obtain ⟨κ, hκ⟩ := hC
  exact hκ.exists_larger σ

/-- 小さい accessible 圏の族は、任意の上限を超える一つの同じ正則濃度で accessible。 -/
@[kerodon 06KP]
lemma exists_common_accessibilityCardinal {ι : Type u} (C : ι → SSet.{u + 1})
    [∀ i, Quasicategory (C i)] (hC : ∀ i, IsAccessible (C i)) (σ : Cardinal.{u}) :
    ∃ μ : Cardinal.{u}, μ.IsRegular ∧ σ < μ ∧ ∀ i, IsKappaAccessible μ (C i) := by
  let κ : ι → Cardinal.{u} := fun i ↦ (hC i).choose
  have hκ (i : ι) : IsKappaAccessible (κ i) (C i) := (hC i).choose_spec
  obtain ⟨μ, hμ, hσ, h⟩ := exists_regular_cardinalChangeBound_family κ σ
  have : Fact μ.IsRegular := ⟨hμ⟩
  exact ⟨μ, hμ, hσ, fun i ↦ (hκ i).of_cardinalChangeBound (h i)⟩

end SerrePositivity.InfinityCategories.F2.Presentable
