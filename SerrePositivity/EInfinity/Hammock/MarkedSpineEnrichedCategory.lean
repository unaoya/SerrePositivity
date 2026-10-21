module

public import SerrePositivity.EInfinity.Hammock.MarkedSpineCompositionLaws
public import Mathlib.CategoryTheory.Enriched.Basic

/-!
# 元の全指定因子列による単体的豊穣圏

概要：元の明示的な合成と指定終端の単位を全因子列の豊穣圏へ束ねる。
方針：証明済みの左右単位則と結合則を元のモノイダル公理の形へ移す。
規約：元の自由圏の対象集合を保持し大域 instance を追加しない。
使われ方：自由積の元の因子列による合成と普遍性。
-/

@[expose] public section
universe u
noncomputable section
namespace SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{u} C] (W : MorphismProperty C)

@[instance_reducible]
def enrichedCategory : EnrichedCategory SSet.{u} (Paths C) where
  Hom X Y := space W Y X
  id := unitMap W
  comp := composition W
  id_comp X Y := by
    rw [← tensorHom_id, composition_left_unit]
    exact Iso.inv_hom_id _
  comp_id X Y := by
    rw [← id_tensorHom, composition_right_unit]
    exact Iso.inv_hom_id _
  assoc X Y Z T := by
    rw [← tensorHom_id, composition_assoc]
    simp only [Iso.inv_hom_id_assoc, id_tensorHom]

end SerrePositivity.EInfinity.Hammock.UnmarkedGenerators.FirstFactor.MarkedSpine
