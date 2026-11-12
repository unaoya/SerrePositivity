module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ComponentCompactGeneralModels
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.PresentableSpanCompactCardinals
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.PullbackSmallColimits

/-!
概要：presentable cospan の元の引き戻し内に小さい native compact 全部分候補圏を構成する。
方針：両関手の共通 compact 保存濃度と、compact 成分の小さい模型を合わせる。
規約：filtered 生成性と引き戻しの presentable 性はこの段階で結論しない。
使われ方：引き戻しの各対象の filtered 表示を接続する生成候補。

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

/-- 概要：元の presentable cospan の引き戻しに、compact 成分の全対象を代表する小さい compact 全部分圏がある。
方針：共通濃度での compact 成分圏の小さい全同値模型を、元の引き戻しへ包含する。
規約：同じ元の引き戻し内の compact 性を供給し、濃度の下限 σ を保持する。
使われ方：filtered 生成性を証明すれば accessibility へ直接接続できる候補。 -/
lemma exists_presentablePullback_compactCandidate
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) (hD : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable D) (hB : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable B)
    (p : E ⟶ B) (q : D ⟶ B) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p)
    (hpc : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits p) (hqc : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits q) (σ : Cardinal.{u}) :
    letI := hp.innerFibration
    ∃ μ : Cardinal.{u}, μ.IsRegular ∧ σ < μ ∧
      ∃ (A : SSet.{u}) (hA : Quasicategory A),
        letI := hA
        ∃ i : (SSet.uliftFunctor.{u + 1, u}).obj A ⟶ pullback p q,
          _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful i ∧
          (∀ a : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (i.app _ (ULift.up a))) ∧
          (∀ a : A _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactVertex μ p q (i.app _ (ULift.up a))) ∧
          ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactVertex μ p q x →
            ∃ a : A _⦋0⦌, Nonempty (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso x (i.app _ (ULift.up a))) := by
  have : InnerFibration p := hp.innerFibration
  obtain ⟨κ, μ, hκ, hμ, hσ, hκμ, he, hd, hb, hpCompact, hqCompact⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_presentableSpan_compactCardinal hE hD hB p q hpc hqc σ
  have : Fact κ.IsRegular := ⟨hκ⟩
  have : Fact μ.IsRegular := ⟨hμ⟩
  obtain ⟨A, hA, ⟨a⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_smallComponentCompactModel he hd hb p q hp hpCompact hqCompact
  have := hA
  let j := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (pullback p q) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactVertex μ p q)).ι
  let i := a.hom ≫ j
  have hfc := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pullback_fst_preservesSmallColimits p q hp hE.2 hD.2 hpc hqc
  have hsc := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pullback_snd_preservesSmallColimits p q hp hE.2 hD.2 hpc hqc
  have hf := hfc.isKappaAccessibleFunctor μ
  have hs := hsc.isKappaAccessibleFunctor μ
  refine ⟨μ, hμ, hσ, A, hA, i,
    a.isQCatEquivalence.isFullyFaithful.comp
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _), ?_, ?_, ?_⟩
  · intro x
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.componentCompactObjects_vertex_isKappaCompact μ p q hκμ hf hs
      (hpc.isKappaAccessibleFunctor μ) hpCompact (a.hom.app _ (ULift.up x))
  · intro x
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices_vertex (a.hom.app _ (ULift.up x))
  · intro x hx
    let xx : (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.componentCompactObjects μ p q) _⦋0⦌ := ⟨x, by
      intro α
      have hα : α = 𝟙 ⦋0⦌ := Subsingleton.elim _ _
      subst α
      simpa only [op_id, CategoryTheory.Functor.map_id_apply] using hx⟩
    refine ⟨(a.inv.app _ xx).down, ⟨?_⟩⟩
    exact ((a.invHomIso.app xx).map j).symm

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
