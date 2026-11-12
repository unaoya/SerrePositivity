module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.ComponentProjectionCofinality
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.CofinalComponentPresentations

/-!
概要：共通の相対構成濃度から元の一般引き戻しの accessibility を構成する。
方針：両成分の cofinal 性、元の密度余錐、compact 生成模型を順に接続する。
規約：元の表示内の交互構成を用い、生成性の存在を追加仮定にしない。
使われ方：元の accessible 圏と関手から共通濃度を選ぶ主定理の最後の段。

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

/-- 概要：共通 κ₀ と μ の相対交互構成により元の引き戻しは μ-accessible。
方針：実際の compact comma の両射影を cofinal と示し、その密度から小さい filtered 生成表示を作る。
規約：全小余極限や生成表示の存在を追加入力にしない。
使われ方：一般 accessible 引き戻しの無条件の濃度選択への接続。 -/
lemma pullback_isKappaAccessible_of_relativeCardinals
    {κ μ : Cardinal.{u}} [Fact κ.IsRegular] [Fact μ.IsRegular]
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.IsCardinalChangeBound κ μ)
    {B : SSet.{u + 1}} [Quasicategory B] (hB : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ B)
    (C : Fin 2 → SSet.{u + 1}) [∀ c, Quasicategory (C c)]
    (hC : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ (C c))
    (hCκ : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ (C c))
    (hBκ : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.HasSmallKappaFilteredColimits κ B)
    (p : ∀ c, C c ⟶ B) (hp : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.EquivalenceLifting (p 0))
    (hpμ : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor μ (p c))
    (hpκ : ∀ c, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessibleFunctor κ (p c))
    (hpCompact : ∀ c, ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ v →
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ ((p c).app (Opposite.op ⦋0⦌) v)) :
    letI := hp.innerFibration
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ (pullback (p 0) (p 1)) := by
  letI := hp.innerFibration
  have hμ : Cardinal.aleph0 < μ :=
    (Cardinal.IsRegular.aleph0_le (Fact.out : κ.IsRegular)).trans_lt h.1
  have hcone := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.hasCompactSliceCocones_of_accessible_components h (p 0) (p 1) hp
    (hC 0) (hC 1) hB (hCκ 0) (hCκ 1) hBκ
    (hpμ 0) (hpμ 1) (hpκ 0) (hpκ 1) (hpCompact 0) (hpCompact 1)
  have hfst := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.componentCompactOverFst_isRightCofinal_of_accessible_family h hB C hC hCκ
    hBκ p hp hpμ hpκ hpCompact
  have hsnd := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.componentCompactOverSnd_isRightCofinal_of_accessible_family h hB C hC hCκ
    hBκ p hp hpμ hpκ hpCompact
  have hpres := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.hasComponentPresentations_of_cofinal_components hμ (p 0) (p 1) hp
    (hC 0) (hC 1) hB (hpμ 0) (hpμ 1) (hpCompact 0) (hpCompact 1) hcone hfst hsnd
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.isKappaAccessible_of_componentPresentations h (hC 0) (hC 1) hB (p 0) (p 1) hp
    (hpμ 0) (hpμ 1) (hpCompact 0) (hpCompact 1) hpres

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
