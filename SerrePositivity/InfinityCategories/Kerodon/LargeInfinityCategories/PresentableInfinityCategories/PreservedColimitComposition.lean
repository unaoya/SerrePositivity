module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.PreservedColimitRestriction
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.LocalLeftKanColimitPreservation

/-!
概要：保存された余極限を cofinal な制限と局所左 Kan 合成に沿って移す。
方針：既存の全余錐制限同値と局所左 Kan の存在・保存を同じ余錐に適用する。
規約：像の余極限を別に選ばず、元の関手による同じ全余錐の像を保つ。
使われ方：P-11 の余積・有限形状・可算列の生成段階を合成する。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：right cofinal な制限は保存された余極限の存在を保ち反映する。
方針：元の圏と像の圏の全余錐制限同値を既存の同時輸送へ渡す。
規約：制限写像の単射性は要求しない。
使われ方：可算列の形状の比較と、局所左 Kan 図式の縮約。 -/
lemma hasPreservedColimit_iff_rightCofinalRestriction
    {A B X Y : SSet.{u}} [Quasicategory B] [Quasicategory X] [Quasicategory Y]
    (U : X ⟶ Y) (i : A ⟶ B) (hi : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.IsRightCofinal i) (F : B ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U F ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U (i ≫ F) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.hasPreservedColimit_iff_nativeRestriction F i U
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.sliceUnderRestrict_equivalence_of_rightCofinal i hi F)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.Cofinality.sliceUnderRestrict_equivalence_of_rightCofinal i hi (F ≫ U))

/-- 概要：局所左 Kan 図式と延長先の保存余極限から元の保存余極限を構成する。
方針：存在定理で選んだ元の余錐へ、同じ局所左 Kan の保存定理を適用する。
規約：全ての局所図式の存在と保存を一つの述語で受け取る。
使われ方：有限部品の余積と可算列による P-11 の生成。 -/
lemma hasPreservedColimit_of_localLeftKan
    {A B X Y : SSet.{u}} [Quasicategory A] [Quasicategory B]
    [Quasicategory X] [Quasicategory Y] (U : X ⟶ Y) (δ : A ⟶ B) (F : A ⟶ X)
    (hlocal : ∀ b, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ F b))
    (hB : ∀ G : B ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U G) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.IndCompletionsOfInfinityCategories.HasPreservedColimit U F := by
  have hl b : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.KanExtensions.leftKanDiagram δ F b) := by
    obtain ⟨c, hc, _⟩ := hlocal b
    exact ⟨c, hc⟩
  obtain ⟨c, hc⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.hasColimit_of_localLeftKan_colimits δ F hl (fun G ↦ by
    obtain ⟨d, hd, _⟩ := hB G
    exact ⟨d, hd⟩)
  exact ⟨c, hc, _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.colimitPreservation_of_localLeftKan δ F U hl
    (fun b d hd ↦ (hlocal b).map_isColimit d hd)
    (fun G d hd ↦ (hB G).map_isColimit d hd) c hc⟩

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
