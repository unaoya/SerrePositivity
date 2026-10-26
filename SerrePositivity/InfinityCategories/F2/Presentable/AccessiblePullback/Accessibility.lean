module

public import SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback.RelativeCardinalAccessibility

/-!
概要：accessible 圏と accessible 関手の一般引き戻しの accessibility を公開する。
方針：共通 κ₀ と μ を選び、元の表示内の相対交互構成と compact 生成表示を使う。
規約：片方の関手の equivalence lifting だけを仮定し、全小余極限保存を要求しない。
使われ方：presentable 引き戻しの系と後続の accessibility の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback

/-- 概要：accessible 圏間の accessible 関手の引き戻しは accessible。
方針：共通濃度で長さ κ₀ の相対交互構成を行い、両成分の密度から生成表示を得る。
規約：p の equivalence lifting を使い、表示や compact 生成性を追加仮定にしない。
使われ方：一般 accessible 引き戻しの公開界面と presentable 版の入力。 -/
lemma pullback_isAccessible
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (p : E ⟶ B) (q : D ⟶ B) (hp : F1B.EquivalenceLifting p)
    (hE : IsAccessible E) (hD : IsAccessible D) (hB : IsAccessible B)
    (hpc : IsAccessibleFunctor p) (hqc : IsAccessibleFunctor q) :
    letI := hp.innerFibration
    IsAccessible (pullback p q) := by
  letI := hp.innerFibration
  obtain ⟨κ, μ, hκ, hμ, _, _, hchange, hEκ, hDκ, hBκ, hpκ, hqκ,
    hEμ, hDμ, hBμ, hpμ, hqμ, hpCompact, hqCompact⟩ :=
    exists_relativeCardinals hE hD hB p q hpc hqc Cardinal.aleph0
  letI : Fact κ.IsRegular := ⟨hκ⟩
  letI : Fact μ.IsRegular := ⟨hμ⟩
  let C : Fin 2 → SSet.{u + 1} := ![E, D]
  letI : ∀ c, Quasicategory (C c) := finitePairSection _
    (show Quasicategory E from inferInstance) (show Quasicategory D from inferInstance)
  let f : ∀ c, C c ⟶ B := finitePairSection _ p q
  have hC : ∀ c, IsKappaAccessible μ (C c) := finitePairSection _ hEμ hDμ
  have hCκ : ∀ c, Ind.HasSmallKappaFilteredColimits κ (C c) := finitePairSection _
    hEκ.hasSmallKappaFilteredColimits hDκ.hasSmallKappaFilteredColimits
  have hfμ : ∀ c, IsKappaAccessibleFunctor μ (f c) := finitePairSection _ hpμ hqμ
  have hfκ : ∀ c, IsKappaAccessibleFunctor κ (f c) := finitePairSection _ hpκ hqκ
  have hfCompact : ∀ c, ∀ v, Compact.IsKappaCompact.{u, u + 1} μ v →
      Compact.IsKappaCompact.{u, u + 1} μ ((f c).app (Opposite.op ⦋0⦌) v) :=
    finitePairSection _ hpCompact hqCompact
  have hresult := pullback_isKappaAccessible_of_relativeCardinals hchange hBμ C hC hCκ
    hBκ.hasSmallKappaFilteredColimits f hp hfμ hfκ hfCompact
  exact ⟨μ, hresult⟩

end SerrePositivity.InfinityCategories.F2.Presentable.AccessiblePullback
