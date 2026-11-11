module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.LocalIndDensity

/-!
概要：一般 accessible 圏の全 compact 始域 slice の標準密度余錐を証明する。
方針：compact 小模型の filtered 局所余極限で Ind 密度を元の固定対象へ移す。
規約：全小余極限を仮定せず、元の対象と元の全 slice を保持する。
使われ方：一般 accessible 引き戻しの両成分の生成表示の余極限性。

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

/-- 概要：accessible 圏の全 compact 始域 slice の元の標準余錐は元の対象の余極限。
方針：元の compact 模型の Ind 密度と filtered 局所余極限の存在を合成する。
規約：元の accessible 性以外に全小余極限を要求しない。
使われ方：compact 成分 comma の cofinal 射影から元の生成表示を回収する。 -/
lemma compactSourceSliceDensityCocone_isColimit_of_isKappaAccessible
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ C)
    (a : (Δ[0] : SSet.{u + 1}) ⟶ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactSourceSliceDensityCocone μ a) := by
  obtain ⟨A, hA, ⟨a₀⟩⟩ := hC.exists_smallCompactModel
  letI := hA
  obtain ⟨e, _, ⟨β⟩⟩ := hC.exists_compactModelIndRepresentation a₀
  obtain ⟨f, hf⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.exists_compactIndYonedaModel a₀ e β
  have hlocal (y : C _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda μ A ≫ e.hom)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.indYoneda μ A ≫ e.hom) ≫ 𝟙 C) y) := by
    rw [← hf]
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.hasColimit_compactModel_leftKanDiagram_of_isKappaAccessible hμ hC f y
  obtain ⟨y, rfl⟩ := SSet.yonedaEquiv.symm.surjective a
  have hc := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.indEquivalenceImage_canonicalColimits_of_local_colimits e hlocal y
  rw [← hf] at hc
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.isColimitCone_iff_restrict_equivalentShape
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactSourceSliceKanComparison f y) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactSourceSliceKanComparison_isQCatEquivalence f y)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactSourceSliceDensityCocone μ (SSet.yonedaEquiv.symm y))).mpr
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.isColimitCone_iff_of_cocone_val_eq _ _ ?_).mpr hc
  change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactSourceSliceKanComparison f y) (𝟙 Δ[0]) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry _ ≫ 𝟙 C
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.compactSourceSliceKanComparison_inclusion, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
