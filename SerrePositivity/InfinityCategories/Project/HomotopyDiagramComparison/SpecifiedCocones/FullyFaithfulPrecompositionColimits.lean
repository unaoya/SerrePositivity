module
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeTransformationEquivalence

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeMappingSpace
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.LeftFibrationFiberComparison
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalMappingPostEquivalence
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.CoconeTransformationRestriction

/-!
概要：前合成の充満忠実性から、元の全余錐の制限の同値性を得る。
方針：定値図式への全変換の比較を終点固定余錐へ移し、全頂点の fiber で判定する。
規約：前合成の本質的全射性は要求しない。
使われ方：elements の初頂点局所化による密度余錐の展開。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 概要：充満忠実な前合成は、元の全余錐空間の制限を同値にする。
方針：全変換の区間 Hom の同値性を、元の余錐比較の可換式で戻す。
規約：任意の元の図式と形状射を固定する。
使われ方：局所化された添字の全余極限の比較。 -/
lemma sliceUnderRestrict_isQCatEquivalence_of_fullyFaithful_pre
    {A B X : SSet.{u}} [Quasicategory X] (i : A ⟶ B)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre i).app X)) (F : B ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict F i) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isQCatEquivalence_of_leftFibration_fibers (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (i ≫ F)) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict F i) rfl
  intro z
  have ht : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.constantTransformationRestriction i F z) :=
    hi.intervalMappingPostOfEq_isQCatEquivalence _ _ _ _
  have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationMap_isQCatEquivalence F z).comp ht
  have hr := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.coconeTransformationMap_restrict i F z
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationMap_isQCatEquivalence (i ≫ F) z).cancel_right
    ((congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence hr).mpr he)

/-- 概要：充満忠実な前合成による同じ全余錐の制限は余極限性を保存し反映する。
方針：構成した全余錐空間の同値で始対象性を比較する。
規約：形状の単射性・同値性は仮定しない。
使われ方：元の密度余極限から bar 入力の余極限への移送。 -/
lemma isColimitCone_iff_restrict_of_fullyFaithful_pre
    {A B X : SSet.{u}} [Quasicategory X] (i : A ⟶ B)
    (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.IsFullyFaithful ((pre i).app X)) {F : B ⟶ X} (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone F) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (c.restrict i) :=
  (sliceUnderRestrict_isQCatEquivalence_of_fullyFaithful_pre i hi F).choose.isInitialVertex_iff c

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
