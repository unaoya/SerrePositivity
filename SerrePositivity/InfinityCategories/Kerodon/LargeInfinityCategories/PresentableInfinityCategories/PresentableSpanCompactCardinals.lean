module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.StrongCompactCardinals
public import SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.Definition

/-!
概要：presentable 圏の余極限保存 cospan に、三成分と関手像の共通 compact 濃度を与える。
方針：三圏の accessibility 濃度を揃え、二つの関手の全 compact 像の保存を同時に得る。
規約：元の圏に固定頂点写像の小ささを仮定しない。
使われ方：Pr^L の引き戻しの小さい compact 成分図式の構成。

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

/-- 概要：余極限保存 cospan の三圏は同じ正則 μ で accessible となり、両関手は全 μ-compact 対象を保つ。
方針：三圏の共通濃度から二関手の共通 compact 保存濃度へ変更する。
規約：指定した上限 σ と明示的な濃度変更条件を保持する。
使われ方：compact 全部分圏の実 cospan と小さい模型を作る。 -/
lemma exists_presentableSpan_compactCardinal
    {E D B : SSet.{u + 1}} [Quasicategory E] [Quasicategory D] [Quasicategory B]
    (hE : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable E) (hD : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable D) (hB : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable B)
    (p : E ⟶ B) (q : D ⟶ B)
    (hp : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits p) (hq : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.PreservesSmallColimits q) (σ : Cardinal.{u}) :
    ∃ κ μ : Cardinal.{u}, κ.IsRegular ∧ μ.IsRegular ∧ σ < μ ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ E ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ D ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ B ∧
      (∀ x : E _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ x →
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (p.app _ x)) ∧
      (∀ y : D _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ y →
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (q.app _ y)) := by
  let C : ULift.{u} (Fin 3) → SSet.{u + 1} := fun i ↦ ![E, D, B] i.down
  have (i : ULift.{u} (Fin 3)) : Quasicategory (C i) := by
    rcases i with ⟨i⟩
    fin_cases i <;> dsimp [C] <;> infer_instance
  have hc : ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsAccessible (C i) := by
    rintro ⟨i⟩
    fin_cases i
    · exact hE.isAccessible
    · exact hD.isAccessible
    · exact hB.isAccessible
  obtain ⟨κ, hκ, _, hC⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_common_accessibilityCardinal C hc σ
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible κ E := hC ⟨0⟩
  have hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible κ D := hC ⟨1⟩
  have hb : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible κ B := hC ⟨2⟩
  obtain ⟨μ, hμ, hσ, hκμ, heμ, hdμ, hpμ, hqμ⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_common_compactPreservingCardinal he hd hb.isAccessible p q
      (hp.isKappaAccessibleFunctor κ) (hq.isKappaAccessibleFunctor κ) σ
  have : Fact μ.IsRegular := ⟨hμ⟩
  exact ⟨κ, μ, hκ, hμ, hσ, hκμ, heμ, hdμ, hb.of_cardinalChangeBound hκμ, hpμ, hqμ⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
