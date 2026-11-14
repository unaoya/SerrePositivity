module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.KanReplacement.FilteredLifting
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration

/-!
概要：通常の filtered 図式の right fibrations の余極限射は right fibration。
方針：提供済みの有限持ち上げ性の余極限保存を、元の正のホーンに適用する。
規約：元の実際の余極限余錐と脚上の等式を保持し、モデル圏の仮定を追加しない。
使われ方：right fibration 模型内の κ-filtered 余極限閉性への入力。

対応節は Kerodon 9.3（Tag 06FR）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories

/-- 元の filtered な right fibrations の図式の実際の余極限射も right fibration。 -/
lemma rightFibration_of_filtered_isColimit
    {I : Type u} [SmallCategory I] [IsFiltered I]
    {F G : I ⥤ SSet.{u}} (η : F ⟶ G) [∀ j, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (η.app j)]
    {cF : Cocone F} (hF : IsColimit cF) {cG : Cocone G} (hG : IsColimit cG)
    (q : cF.pt ⟶ cG.pt) (hq : ∀ j, cF.ι.app j ≫ q = η.app j ≫ cG.ι.app j) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration q where
  mem := by
    intro A B f hf
    cases hf with
    | @intro n i hi =>
      have (j : I) : HasLiftingProperty (horn (n + 1) i).ι (η.app j) :=
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration.mem _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightHornInclusions.intro i hi)
      exact _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.hasLiftingProperty_of_filtered_isColimit η hF hG q hq _

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories
