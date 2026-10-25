module

public import SerrePositivity.InfinityCategories.F2.Ind.PreservedColimitRestriction
public import SerrePositivity.InfinityCategories.F2.Presentable.LocalLeftKanColimitPreservation

/-!
概要：保存された余極限を cofinal な制限と局所左 Kan 合成に沿って移す。
方針：既存の全余錐制限同値と局所左 Kan の存在・保存を同じ余錐に適用する。
規約：像の余極限を別に選ばず、元の関手による同じ全余錐の像を保つ。
使われ方：P-11 の余積・有限形状・可算列の生成段階を合成する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：right cofinal な制限は保存された余極限の存在を保ち反映する。
方針：元の圏と像の圏の全余錐制限同値を既存の同時輸送へ渡す。
規約：制限写像の単射性は要求しない。
使われ方：可算列の形状の比較と、局所左 Kan 図式の縮約。 -/
lemma hasPreservedColimit_iff_rightCofinalRestriction
    {A B X Y : SSet.{u}} [Quasicategory B] [Quasicategory X] [Quasicategory Y]
    (U : X ⟶ Y) (i : A ⟶ B) (hi : IsRightCofinal i) (F : B ⟶ X) :
    Ind.HasPreservedColimit U F ↔ Ind.HasPreservedColimit U (i ≫ F) :=
  Ind.hasPreservedColimit_iff_nativeRestriction F i U
    (Ind.sliceUnderRestrict_equivalence_of_rightCofinal i hi F)
    (Ind.sliceUnderRestrict_equivalence_of_rightCofinal i hi (F ≫ U))

/-- 概要：局所左 Kan 図式と延長先の保存余極限から元の保存余極限を構成する。
方針：存在定理で選んだ元の余錐へ、同じ局所左 Kan の保存定理を適用する。
規約：全ての局所図式の存在と保存を一つの述語で受け取る。
使われ方：有限部品の余積と可算列による P-11 の生成。 -/
lemma hasPreservedColimit_of_localLeftKan
    {A B X Y : SSet.{u}} [Quasicategory A] [Quasicategory B]
    [Quasicategory X] [Quasicategory Y] (U : X ⟶ Y) (δ : A ⟶ B) (F : A ⟶ X)
    (hlocal : ∀ b, Ind.HasPreservedColimit U (leftKanDiagram δ F b))
    (hB : ∀ G : B ⟶ X, Ind.HasPreservedColimit U G) :
    Ind.HasPreservedColimit U F := by
  have hl b : HasColimit (leftKanDiagram δ F b) := by
    obtain ⟨c, hc, _⟩ := hlocal b
    exact ⟨c, hc⟩
  obtain ⟨c, hc⟩ := hasColimit_of_localLeftKan_colimits δ F hl (fun G ↦ by
    obtain ⟨d, hd, _⟩ := hB G
    exact ⟨d, hd⟩)
  exact ⟨c, hc, colimitPreservation_of_localLeftKan δ F U hl
    (fun b d hd ↦ (hlocal b).map_isColimit d hd)
    (fun G d hd ↦ (hB G).map_isColimit d hd) c hc⟩

end SerrePositivity.InfinityCategories.F2.Presentable
