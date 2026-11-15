module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.NerveLeftQuillenA
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.WeakContractibleContractionCospan
public import Mathlib.CategoryTheory.Adjunction.Comma
public import Mathlib.CategoryTheory.Adjunction.Opposites

/-!
概要：通常の左随伴の nerve は極限を計算する向きの left cofinal 射である。
方針：各左 comma の終対象で nerve を収縮し、通常の comma による Quillen A を使う。
使われ方：Kerodon §7.2（Tag 02N1）、HTT §4.1 の cofinal な形状比較。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory CategoryTheory.Limits
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality

/-- 元の左随伴の各左 comma は余単位を終対象に持ち、その nerve は弱可縮。 -/
lemma nerveMap_isLeftCofinal_of_adjunction {C D : Type u}
    [SmallCategory C] [SmallCategory D] {F : C ⥤ D} {G : D ⥤ C}
    (h : F ⊣ G) : IsLeftCofinal (nerveMap F) := by
  apply nerveMap_isLeftCofinal_of_weaklyContractible_comma
  intro d
  let c : CostructuredArrow F d := CostructuredArrow.mk (h.counit.app d)
  let hc : IsTerminal c := mkTerminalOfRightAdjoint G h d
  exact SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.nerve_isWeaklyContractible_of_contractionCospan
    c ((Functor.const _).obj c)
    { app := fun a => hc.from a
      naturality := by intros; apply hc.hom_ext }
    (𝟙 _)

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality
