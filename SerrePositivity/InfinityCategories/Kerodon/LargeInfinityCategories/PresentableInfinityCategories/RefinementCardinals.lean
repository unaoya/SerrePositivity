module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ArrowCardinals

/-!
概要：小さい部分余極限の交換に必要な濃度変更境界を、生成射の共通濃度に追加する。
方針：実証済み accessibility の濃度と指定濃度の双方に対する境界を取り直す。
規約：濃度の大小だけで accessibility を移さず、正当な境界によって移す。
使われ方：HTT 5.5.4.13–14 の compact 部分表示の濃度の選択。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {C : SSet.{u + 1}} [Quasicategory C] {I : Type u}

/-- 指定濃度からの交換境界を持つ、元の圏と射圏と全生成端点の共通正則濃度。 -/
lemma exists_regular_refinementArrowCardinal (hC : _root_.SerrePositivity.InfinityCategories.HTT.PresentableInfinityCategories.IsPresentable C)
    (edges : I → C _⦋1⦌) (ρ σ : Cardinal.{u}) :
    ∃ μ : Cardinal.{u}, μ.IsRegular ∧ σ < μ ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound ρ μ ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ C ∧
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ ((ihom (Δ[1] : SSet.{u + 1})).obj C) ∧
      (∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.generatorArrowVertex edges i)) ∧
      ∀ i, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (C.δ 1 (edges i)) ∧
        _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (C.δ 0 (edges i)) := by
  obtain ⟨κ, hκ, _, hCκ, hArκ, hgen, hend⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_regular_generatorArrowCardinal hC edges σ
  let family : ULift.{u} Bool → Cardinal.{u} := fun b ↦ if b.down then κ else ρ
  obtain ⟨μ, hμ, hσ, hb⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_regular_cardinalChangeBound_family family σ
  have : Fact κ.IsRegular := ⟨hκ⟩
  have : Fact μ.IsRegular := ⟨hμ⟩
  have hκμ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ := hb ⟨true⟩
  exact ⟨μ, hμ, hσ, hb ⟨false⟩, hCκ.of_cardinalChangeBound hκμ,
    hArκ.of_cardinalChangeBound hκμ, fun i ↦ (hgen i).of_le hκμ.le,
    fun i ↦ ⟨((hend i).1).of_le hκμ.le, ((hend i).2).of_le hκμ.le⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
