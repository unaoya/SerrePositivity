module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.RelativeCardinalAccessibility

/-!
概要：accessible 圏と accessible 関手の一般引き戻しの accessibility を公開する。
方針：共通 κ₀ と μ を選び、元の表示内の相対交互構成と compact 生成表示を使う。
規約：片方の関手の equivalence lifting だけを仮定し、全小余極限保存を要求しない。
使われ方：presentable 引き戻しの系と後続の accessibility の構成。

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

/-- 概要：accessible 圏間の accessible 関手の引き戻しは accessible。
方針：共通濃度で長さ κ₀ の相対交互構成を行い、両成分の密度から生成表示を得る。
規約：p の equivalence lifting を使い、表示や compact 生成性を追加仮定にしない。
使われ方：一般 accessible 引き戻しの公開界面と presentable 版の入力。 -/
lemma pullback_isAccessible
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting p)
    (hE : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible E) (hD : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible D) (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible B)
    (hpc : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor p) (hqc : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessibleFunctor q) :
    letI := hp.innerFibration
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible (pullback p q) := by
  letI := hp.innerFibration
  obtain ⟨κ, μ, hκ, hμ, _, _, hchange, hEκ, hDκ, hBκ, hpκ, hqκ,
    hEμ, hDμ, hBμ, hpμ, hqμ, hpCompact, hqCompact⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_relativeCardinals hE hD hB p q hpc hqc Cardinal.aleph0
  letI : Fact κ.IsRegular := ⟨hκ⟩
  letI : Fact μ.IsRegular := ⟨hμ⟩
  let C : Fin 2 → SSet.{u + 1} := ![E, D]
  letI : ∀ c, Quasicategory (C c) := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.finitePairSection _
    (show Quasicategory E from inferInstance) (show Quasicategory D from inferInstance)
  let f : ∀ c, C c ⟶ B := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.finitePairSection _ p q
  have hC : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ (C c) := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.finitePairSection _ hEμ hDμ
  have hCκ : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ (C c) := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.finitePairSection _
    hEκ.hasSmallKappaFilteredColimits hDκ.hasSmallKappaFilteredColimits
  have hfμ : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ (f c) := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.finitePairSection _ hpμ hqμ
  have hfκ : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (f c) := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.finitePairSection _ hpκ hqκ
  have hfCompact : ∀ c, ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ v →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ ((f c).app (Opposite.op ⦋0⦌) v) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.finitePairSection _ hpCompact hqCompact
  have hresult := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.pullback_isKappaAccessible_of_relativeCardinals hchange hBμ C hC hCκ
    hBκ.hasSmallKappaFilteredColimits f hp hfμ hfκ hfCompact
  exact ⟨μ, hresult⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
