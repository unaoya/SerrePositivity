module

public import SerrePositivity.EInfinity.FrameHom.FrameArrowCategory
public import SerrePositivity.InfinityCategories.F1B.KanNerveLeftKanShapeIso
public import SerrePositivity.InfinityCategories.F1B.KanNerveTerminal
public import SerrePositivity.InfinityCategories.F1B.InitialTerminalWeakContractibility
public import SerrePositivity.InfinityCategories.F1B.QuillenALeft
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
    IsLeftCofinal (nerveMap L) := by
  apply isLeftCofinal_of_weaklyContractible_slices
  intro z
  obtain ⟨d, rfl⟩ := ComposableArrows.mk₀_surjective z
  have ht := mkTerminalOfRightAdjoint R a d
  have hn := (F1B.kanNerveVertex_isTerminal ht).isWeaklyContractible
  have he : IsWeakHomotopyEquivalence (F1B.kanNerveLeftKanShapeIso L d).hom :=
    IsPrecompositionEquivalence.isWeakHomotopyEquivalence
      (isPrecompositionEquivalence_of_iso (F1B.kanNerveLeftKanShapeIso L d))
  exact he.weaklyContractible_iff.mp hn

variable {I C : Type u} [Category.{u} I] [Category.{u} C] (A : I ⥤ C)

lemma identityInclusion_nerve_isLeftCofinal : IsLeftCofinal (nerveMap (identityInclusion A)) :=
  nerveMap_leftAdjoint_isLeftCofinal (identityDegreeAdjunction A)

end SerrePositivity.EInfinity.FrameHom.FrameArrows
