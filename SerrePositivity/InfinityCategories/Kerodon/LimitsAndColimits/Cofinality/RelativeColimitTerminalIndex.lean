module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.TerminalPointAnodyne
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.LeftKanIdentityVertex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.RelativeColimitReindex
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.CosliceRestriction

/-!
概要：終対象への一点制限による標準相対余極限の判定。
方針：終対象包含の right anodyne 性と二つの coslice 制限の自明 Kan 性を使う。
規約：U の充填性は要求しない。
使われ方：全部分圏の像の点で Kan の相対局所余錐を恒等射の脚へ制限する。

対応節は Kerodon 7.2（Tag 02MZ）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 概要：right anodyne な添字変更は標準 U 余極限を保ち反映する。
方針：両 coslice の制限の充満忠実性と頂点全射性で相対始対象性を比較する。
規約：U に inner fibration 性を要求しない。
使われ方：終対象包含に沿う相対局所余錐の一点への還元。 -/
lemma kanIsRelativeColimitCone_iff_restrict_of_rightAnodyne
    {A J D E : SSet.{u}} [Quasicategory D] [Quasicategory E]
    (U : D ⟶ E) {p : J ⟶ D} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (i : A ⟶ J) [Mono i]
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions i) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U (c.restrict i) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict_trivialKanFibration p i hi
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict_trivialKanFibration (p ≫ U) i hi
  obtain ⟨s, hs⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.trivialKanFibration_exists_section (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict p i)
  have hsurj : Function.Surjective ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict p i).app (Opposite.op ⦋0⦌)) := by
    intro y
    exact ⟨s.app (Opposite.op ⦋0⦌) y,
      ConcreteCategory.congr_hom (NatTrans.congr_app hs (Opposite.op ⦋0⦌)) y⟩
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanRelativeInitialVertex_iff_of_comparison
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp p U) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderPostcomp (i ≫ p) U)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict p i) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict (p ≫ U) i)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict_postcomp p i U).symm
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _).isFullyFaithful
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.isQCatEquivalence_of_trivialKanFibration _).isFullyFaithful hsurj c

/-- 概要：終対象を持つ添字上の標準相対余極限はその終対象での脚で判定できる。
方針：終対象を選ぶ一点の包含に沿って相対余錐を制限する。
規約：添字 J の quasicategory 性は不要。
使われ方：Kan 単位の可逆性のための局所入力を一点図式へ移す。 -/
lemma kanIsRelativeColimitCone_iff_restrict_terminal {J D E : SSet.{u}}
    [Quasicategory D] [Quasicategory E] (U : D ⟶ E)
    {p : J ⟶ D} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (t : J _⦋0⦌) (ht : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex t) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U (c.restrict (SSet.yonedaEquiv.symm t)) := by
  have := _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.cofinalPointInclusion_mono t
  exact kanIsRelativeColimitCone_iff_restrict_of_rightAnodyne U c _
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.terminalPoint_rightAnodyne ht)

/-- 概要：充満忠実な inner 包含の像では標準相対 Kan 余錐を恒等射の脚で判定できる。
方針：局所添字の恒等射の終対象性を一点制限の判定へ渡す。
規約：元の図式 F₀ と候補の頂点を保つ同じ余錐を制限する。
使われ方：相対 Kan の局所条件から単位の成分の可逆性を導く。 -/
lemma kanLeftLocalColimit_iff_restrict_identity {K C D E : SSet.{u}}
    [Quasicategory K] [Quasicategory C] [Quasicategory D] [Quasicategory E]
    (δ : K ⟶ C) [InnerFibration δ] (hδ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful δ) (U : D ⟶ E)
    (F₀ : K ⟶ D) (k : K _⦋0⦌)
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ F₀ (δ.app (Opposite.op ⦋0⦌) k))) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U c ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsRelativeColimitCone U (c.restrict (SSet.yonedaEquiv.symm (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanIdentityVertex δ k))) :=
  kanIsRelativeColimitCone_iff_restrict_terminal U c _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.kanLeftKanIdentityVertex_isTerminal δ hδ k)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "4.3.1.7" (partial := stronger-hyp) "仮定：内ファイブレーション上の余錐と共終な添字変更（Lean が強い：添字変更は右アノダインな単射）。結論：同じ余錐の制限前後で相対余極限性が同値（一致）。"] _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.kanIsRelativeColimitCone_iff_restrict_of_rightAnodyne
