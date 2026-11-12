module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FrameArrowCategory
public import SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.LeftKanShapeIso
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Terminal
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.InitialTerminalWeakContractibility
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.QuillenALeft
public import Mathlib.CategoryTheory.Adjunction.Comma

/-!
# 元の恒等矢の包含の ∞ 圏的 left cofinal 性

概要：元の随伴の counit が指定する各 comma の終対象で Quillen A を検査する。
方針：通常の comma の nerve と既存の native slice の同型を使う。
規約：通常の initial 性だけで代用せず、元の nerve 写像自身の cofinal 性を証明する。
使われ方：source frame の全矢の局所極限を次数圏へ制限する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom.FrameArrows
open CategoryTheory SerrePositivity.InfinityCategories
open scoped Simplicial

lemma nerveMap_leftAdjoint_isLeftCofinal {I D : Type u}
    [Category.{u} I] [Category.{u} D] {L : I ⥤ D} {R : D ⥤ I} (a : L ⊣ R) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (nerveMap L) := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.isLeftCofinal_of_weaklyContractible_slices
  intro z
  obtain ⟨d, rfl⟩ := ComposableArrows.mk₀_surjective z
  have ht := mkTerminalOfRightAdjoint R a d
  have hn := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.nerveVertex_isTerminal ht).isWeaklyContractible
  have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsWeakHomotopyEquivalence (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeIso L d).hom :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsPrecompositionEquivalence.isWeakHomotopyEquivalence
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.isPrecompositionEquivalence_of_iso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.NerveComparison.nerveLeftKanShapeIso L d))
  exact he.weaklyContractible_iff.mp hn

variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C)

lemma identityInclusion_nerve_isLeftCofinal : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsLeftCofinal (nerveMap (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FrameArrowCategory.identityInclusion A)) :=
  nerveMap_leftAdjoint_isLeftCofinal (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FrameArrowCategory.identityDegreeAdjunction A)

end SerrePositivity.EInfinity.FrameHom.FrameArrows
