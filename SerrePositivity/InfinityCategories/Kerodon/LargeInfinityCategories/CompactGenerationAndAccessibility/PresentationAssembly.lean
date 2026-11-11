module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.Cardinals
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.PartialColimits
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FiberAccessibility
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.PullbackSmallColimits

/-!
概要：元の各対象の compact 両成分表示を、小生成模型の accessibility へ接続する。
方針：既存の全 compact 成分小模型へ同じ全表示を移し、元の余錐頂点を厳密に回収する。
規約：本葉は生成表示からの接続。生成表示自体の存在は相対交互構成で別途証明する。
使われ方：一般版の最後の組み立てと presentable 系。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility


/-- 概要：元の各対象が μ-compact 両成分の全 filtered 表示を持つこと。
方針：同じ元の引き戻しと指定余錐頂点を量化する。
規約：生成性の未証明部分を存在公理へ置き換えない。
使われ方：相対交互構成の出力を最後の小模型へ渡す。 -/
def HasComponentPresentations (μ : Cardinal.{u})
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) : Prop :=
  ∀ x : (pullback p q) _⦋0⦌,
    ∃ (M : SSet.{u}) (hM : Quasicategory M), letI := hM
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ M ∧
      ∃ F : (SSet.uliftFunctor.{u + 1, u}).obj M ⟶ pullback p q,
        (∀ k, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactVertex μ p q (F.app (Opposite.op ⦋0⦌) k)) ∧
        ∃ c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ∧ c.vertex = x

/-- 概要：同じ濃度の compact 両成分生成表示から元の引き戻しの accessibility を得る。
方針：compact 成分の小模型へ同じ全表示を移し、頂点を保つ余錐同型を使う。
規約：元の生成表示を入力に取る組み立て補題。
使われ方：相対交互構成の生成性証明後の主定理の最後の段。 -/
lemma isKappaAccessible_of_componentPresentations
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (hκμ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ)
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ E) (hD : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ D) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ B)
    (p : E ⟶ B) (q : D ⟶ B) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p)
    (hpc : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ p) (hqc : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ q)
    (hpCompact : ∀ x, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ x →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (p.app _ x))
    (hqCompact : ∀ y, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ y →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (q.app _ y))
    (hpres : HasComponentPresentations μ p q) :
    letI := hp.innerFibration
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ (pullback p q) := by
  have : InnerFibration p := hp.innerFibration
  obtain ⟨A, hA, ⟨a⟩⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_smallComponentCompactModel hE hD hB p q hp hpCompact hqCompact
  have := hA
  let P := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.ComponentCompactVertex μ p q
  let j := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexOnVertices (pullback p q) P).ι
  let i := a.hom ≫ j
  have hf := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.pullback_fst_isKappaAccessibleFunctor p q hp
    hE.hasSmallKappaFilteredColimits hD.hasSmallKappaFilteredColimits hpc hqc
  have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.pullback_snd_isKappaAccessibleFunctor p q hp
    hE.hasSmallKappaFilteredColimits hD.hasSmallKappaFilteredColimits hpc hqc
  refine ⟨Fact.out, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.pullback_hasSmallKappaFilteredColimits p q hp
    hE.hasSmallKappaFilteredColimits hD.hasSmallKappaFilteredColimits hpc hqc, A, hA, i,
    a.isQCatEquivalence.isFullyFaithful.comp
      (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.isFullyFaithful_fullSubcomplexOnVertices_ι _ _), ?_, ?_⟩
  · intro v
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.componentCompactObjects_vertex_isKappaCompact μ p q hκμ hf hs hpc hpCompact
      (a.hom.app _ (ULift.up v))
  · intro x
    obtain ⟨M, hM, hfiltered, F, hF, c, hc, hv⟩ := hpres x
    have := hM
    have := hfiltered
    let H := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift P F hF
    let b := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown (H ≫ a.inv)
    have hb : (SSet.uliftFunctor.{u + 1, u}).map b = H ≫ a.inv := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.uliftMorphismDown_lift _
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso ((SSet.uliftFunctor.{u + 1, u}).map b ≫ i) F := by
      rw [hb]
      simpa only [i, Category.assoc, Category.id_comp, H, j, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.fullSubcomplexLift_ι] using
        (a.invHomIso.precomp H).postcomp j
    obtain ⟨c', hc', hv'⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits.exists_colimitCocone_functorIso_sameVertex he.symm c hc
    exact ⟨M, hM, hfiltered, b, c', hv'.trans hv, hc'⟩

/-- 概要：accessible な実引き戻しに全小余極限保存を加えると presentable。
方針：既存の実引き戻しの小余極限構成と accessibility を合わせる。
規約：本葉では accessibility を入力に取り、一般版を未証明のまま主張しない。
使われ方：一般版の accessibility からの presentable 系の最終接続。 -/
lemma isPresentable_of_isAccessible
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits E) (hD : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.HasSmallColimits D)
    (p : E ⟶ B) (q : D ⟶ B) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p)
    (hpc : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits p) (hqc : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits q) :
    letI := hp.innerFibration
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible (pullback p q) → _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable (pullback p q) := by
  have : InnerFibration p := hp.innerFibration
  intro ha
  exact ⟨ha, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.pullback_hasSmallColimits p q hp hE hD hpc hqc⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
