module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.StableInputColimits

/-!
概要：入力と標的を固定する compact 成分表示の具体的データ。
方針：構成済みの正規化表示を同じ小添字・全余錐・compact 性の組として保持する。
規約：構造の存在は accessible 性から証明し、追加入力の存在仮定にしない。
使われ方：相対交互構成の元の両成分表示の一括入力。

対応節は Kerodon 9.4（Tag 06GT）。
-/

@[expose] public section
noncomputable section
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility

/-- 概要：入力図式の下かつ元の標的の上の compact filtered 全表示。
方針：同じ小添字と同じ全増大余錐の元の底への射影を保持する。
規約：元の圏の compact 性で判定する。
使われ方：元の両成分を共通の底の全交互塔へ送る。 -/
structure CompactInputPresentation (μ : Cardinal.{u})
    {K C : SSet.{u + 1}} [Quasicategory C] (q : K ⟶ C) (z : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) where
  index : SSet.{u}
  index_quasicategory : Quasicategory index
  index_filtered : @_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FilteredInfinityCategories.IsKappaFiltered μ index index_quasicategory
  diagram : (SSet.uliftFunctor.{u + 1, u}).obj index ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOver ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder q)).symm z)
  compact : ∀ v : index _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ
    ((diagram ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection ((SSet.yonedaEquiv (X := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder q)).symm z) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection q).app (Opposite.op ⦋0⦌) (ULift.up v))
  colimit : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sliceDiagramCocone diagram)
  colimit_base : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.mapJoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection q) (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.sliceDiagramCocone diagram))

attribute [instance] CompactInputPresentation.index_quasicategory
attribute [instance] CompactInputPresentation.index_filtered

/-- 概要：accessible 圏の小さい compact 入力図式の元の余錐は compact 全表示を持つ。
方針：元の compact 生成表示の正規化で全データを構成する。
規約：全小余極限の仮定や新しい存在公理を追加しない。
使われ方：元の両成分表示を同時に選ぶ。 -/
lemma nonempty_compactInputPresentation_of_isKappaAccessible
    {μ : Cardinal.{u}} [Fact μ.IsRegular] (hμ : Cardinal.aleph0 < μ)
    {C : SSet.{u + 1}} [Quasicategory C] (hC : _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.IsKappaAccessible μ C)
    {K : SSet.{u}} [Quasicategory K] (hK : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.SizeConditionsOnInfinityCategories.IsKappaSmall μ K)
    (q : (SSet.uliftFunctor.{u + 1, u}).obj K ⟶ C)
    (hq : ∀ v, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.FinitaryFunctorsAndCompactObjects.IsKappaCompact.{u, u + 1} μ (q.app (Opposite.op ⦋0⦌) v))
    (z : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone q) : Nonempty (CompactInputPresentation μ q z) := by
  obtain ⟨I, hI, hf, P, hP, hc, hb⟩ :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility.exists_compactSourceSlicePresentation_of_isKappaAccessible hμ hC hK q hq z
  exact ⟨⟨I, hI, hf, P, hP, hc, hb⟩⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.CompactGenerationAndAccessibility
