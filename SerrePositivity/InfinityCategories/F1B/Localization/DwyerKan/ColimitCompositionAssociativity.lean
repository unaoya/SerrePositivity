module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.GraphCompositionAssociativity
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.TripleColimit

/-!
# 元の全語の余極限上の合成の結合則

概要：実際の三つの余極限の積上で、元の合成の結合則を証明する。
方針：外部積余錐の一意性を使い、元の全固定語の graph の結合則へ帰着する。
規約：元の合成・標準射を保持し、filtered 性や単体集合のモデル構造は使わない。
使われ方：hammock の実際の単体的豊穣圏。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (X Y Z V : C)

lemma colimitComposition_assoc_left_fac (a b c : Word) :
    ((graphInclusion W X Y a ⊗ₘ graphInclusion W Y Z b) ⊗ₘ graphInclusion W Z V c) ≫
        (colimitComposition W X Y Z ⊗ₘ 𝟙 (colimitGraph W Z V)) ≫
          colimitComposition W X Z V =
      (graphComposition W a b X Y Z ⊗ₘ 𝟙 (graph W c Z V)) ≫
        graphComposition W (Word.append a b) c X Z V ≫
          graphInclusion W X V (Word.append (Word.append a b) c) := by
  rw [tensorHom_comp_tensorHom_assoc, Category.comp_id, colimitComposition_fac]
  dsimp only [graphPairing]
  rw [← Category.id_comp (graphInclusion W Z V c), ← tensorHom_comp_tensorHom_assoc,
    colimitComposition_fac]
  rfl

lemma colimitComposition_assoc_right_fac (a b c : Word) :
    ((graphInclusion W X Y a ⊗ₘ graphInclusion W Y Z b) ⊗ₘ graphInclusion W Z V c) ≫
        (α_ (colimitGraph W X Y) (colimitGraph W Y Z) (colimitGraph W Z V)).hom ≫
          (𝟙 (colimitGraph W X Y) ⊗ₘ colimitComposition W Y Z V) ≫
            colimitComposition W X Y V =
      (α_ (graph W a X Y) (graph W b Y Z) (graph W c Z V)).hom ≫
        (𝟙 (graph W a X Y) ⊗ₘ graphComposition W b c Y Z V) ≫
          graphComposition W a (Word.append b c) X Y V ≫
            graphInclusion W X V (Word.append a (Word.append b c)) := by
  rw [associator_naturality_assoc, tensorHom_comp_tensorHom_assoc, Category.comp_id,
    colimitComposition_fac]
  dsimp only [graphPairing]
  rw [← Category.id_comp (graphInclusion W X Y a), ← tensorHom_comp_tensorHom_assoc,
    colimitComposition_fac]
  rfl

/-- 元の三つの余極限の積からの、実際の合成の結合則。 -/
lemma colimitComposition_assoc :
    (colimitComposition W X Y Z ⊗ₘ 𝟙 (colimitGraph W Z V)) ≫ colimitComposition W X Z V =
      (α_ (colimitGraph W X Y) (colimitGraph W Y Z) (colimitGraph W Z V)).hom ≫
        (𝟙 (colimitGraph W X Y) ⊗ₘ colimitComposition W Y Z V) ≫
          colimitComposition W X Y V := by
  apply tensorTriple_hom_ext W X Y Z V
  intro a b c
  rw [colimitComposition_assoc_left_fac, colimitComposition_assoc_right_fac]
  rw [← graphInclusion_naturality W X V (eqToHom (Word.append_assoc a b c))]
  simpa only [Category.assoc] using congrArg
    (fun f => f ≫ graphInclusion W X V (Word.append a (Word.append b c)))
    (graphComposition_assoc W a b c X Y Z V)

end SerrePositivity.EInfinity.Hammock
