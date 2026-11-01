module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ColimitCompositionAssociativity
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.ColimitCompositionUnit
public import Mathlib.CategoryTheory.Enriched.Basic

/-!
# 全語の実際の余極限による hammock の単体的豊穣圏

概要：元の余極限・空語の単位・連結の合成を、全公理を満たす豊穣圏へ束ねる。
方針：構成済みの左右単位則と結合則をモノイダル構造の形式へ移す。
規約：大域 instance は追加せず、元の圏の対象集合と弱同値を保持する。
使われ方：縮約 hammock・既存 DK 局所化との高次比較。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]

/-- 同じ元の対象上の、全語の余極限による実際の単体的豊穣圏。 -/
@[instance_reducible]
def enrichedCategory : EnrichedCategory SSet.{max u v} C where
  Hom := colimitGraph W
  id := colimitUnit W
  comp := colimitComposition W
  id_comp X Y := by
    rw [← tensorHom_id, colimitComposition_left_unit]
    exact Iso.inv_hom_id _
  comp_id X Y := by
    rw [← id_tensorHom, colimitComposition_right_unit]
    exact Iso.inv_hom_id _
  assoc X Y Z V := by
    rw [← tensorHom_id, colimitComposition_assoc]
    simp only [Iso.inv_hom_id_assoc, id_tensorHom]

lemma enrichedCategory_hom (X Y : C) :
    (enrichedCategory W).Hom X Y = colimitGraph W X Y := rfl

lemma enrichedCategory_id (X : C) :
    (enrichedCategory W).id X = colimitUnit W X := rfl

lemma enrichedCategory_comp (X Y Z : C) :
    (enrichedCategory W).comp X Y Z = colimitComposition W X Y Z := rfl

end SerrePositivity.EInfinity.Hammock
