module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeInitialComparison
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.RelativeInitialBoundaryCriterion

/-!
概要：標準の U 余極限条件と図式固定の余錐の族の相対普遍性の同値。
方針：coslice 比較の自然性と頂点全射性で相対始対象性を移し、inner fibration の境界判定を使う。
規約：全余錐を動かす相対制限の条件への移行は別に証明する。
使われ方：標準の相対 Kan 条件から操作的な充填を回収するための fiber の判定。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits

/-- 概要：図式固定の余錐の族の後合成は U が inner fibration なら inner fibration。
方針：全余錐の相対制限の内ホーン充填を図式の頂点 fiber に制限する。
規約：添字と値域の quasicategory 性は不要。
使われ方：標準 U 余極限条件から固定図式の厳密な境界充填を得る。 -/
instance kanCoconeFamilyPostcomp_innerFibration {K D E : SSet.{u}}
    (p : K ⟶ D) (U : D ⟶ E) [InnerFibration U] :
    InnerFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCoconeFamilyPostcomp p U) := by
  exact @_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeVertexFiberMap_innerFibration _ _ _ _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K D) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeRestriction K E)
    ((ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join K (Δ[0] : SSet.{u}))).map U) ((ihom K).map U)
    ((pre (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (Δ[0] : SSet.{u}))).naturality U).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeCoconeRestriction_innerFibration K U) (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex p)

/-- 概要：標準の U 余極限条件は固定図式の余錐の族での相対始対象性と同値。
方針：coslice 比較は充満忠実で頂点に全射であり、後合成と厳密に可換である。
規約：U の充填性は要求しない。
使われ方：相対余極限の標準的な定義と関手の族の fiber の比較。 -/
lemma kanIsRelativeColimitCone_iff_family_relativeInitial {K D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) {p : K ⟶ D} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U c ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.KanRelativeInitialVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCoconeFamilyPostcomp p U) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamilyVertexEquiv p c) := by
  have hs : Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cosliceCoconeFamilyMap p).app (Opposite.op ⦋0⦌)) := by
    intro y
    obtain ⟨d, hd⟩ := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamilyVertexEquiv p).surjective y
    exact ⟨d, (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cosliceCoconeFamilyMap_app_zero p d).trans hd⟩
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeInitialVertex_iff_of_comparison
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p U) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCoconeFamilyPostcomp p U)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cosliceCoconeFamilyMap p) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cosliceCoconeFamilyMap (p ≫ U))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCosliceCoconeFamilyMap_postcomp p U)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_cosliceCoconeFamilyMap p).isFullyFaithful
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isQCatEquivalence_cosliceCoconeFamilyMap (p ≫ U)).isFullyFaithful hs c
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.cosliceCoconeFamilyMap_app_zero] at h
  exact h

/-- 概要：inner fibration 上の標準 U 余極限条件は図式固定の始点境界充填と同値。
方針：相対始対象性を余錐の族へ移し、inner fibration の厳密な境界判定を合成する。
規約：全図式を動かす相対余錐制限への移送はこの結論に含めない。
使われ方：標準の局所相対余極限から coherent な組み立てへ進む fiber の入力。 -/
lemma kanIsRelativeColimitCone_iff_family_initialBoundary {K D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E) [InnerFibration U]
    {p : K ⟶ D} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U c ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InitialBoundaryLifting (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCoconeFamilyPostcomp p U) (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeFamilyVertexEquiv p c) :=
  (kanIsRelativeColimitCone_iff_family_relativeInitial U c).trans
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.kanRelativeInitialVertex_iff_initialBoundary (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanCoconeFamilyPostcomp p U) _)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
