module

public import SerrePositivity.EInfinity.Hammock.ColimitComposition
public import SerrePositivity.EInfinity.Hammock.GraphCompositionUnit

/-!
# 元の全語の余極限上の合成の左右単位則

概要：同じ元の空語の単位と二つの余極限の積からの合成は、左右の単位則を満たす。
方針：全固定語で元の合成を回収し、語の単位遷移の余錐条件から余極限へ降下する。
規約：添字圏の filtered 性・単体集合のモデル構造は要求しない。
使われ方：hammock の実際の豊穣圏の単位公理。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.EInfinity.Hammock
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (X Y : C)

lemma colimitComposition_left_unit_fac (a : Word) :
    (colimitUnit W X ⊗ₘ graphInclusion W X Y a) ≫ colimitComposition W X X Y =
      (λ_ (graph W a X Y)).hom ≫ graphInclusion W X Y a := by
  calc
    _ = (graphUnit W X ⊗ₘ 𝟙 (graph W a X Y)) ≫
        (graphInclusion W X X Word.empty ⊗ₘ graphInclusion W X Y a) ≫
          colimitComposition W X X Y := by
      rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
      rfl
    _ = (graphUnit W X ⊗ₘ 𝟙 (graph W a X Y)) ≫
        graphComposition W Word.empty a X X Y ≫ graphInclusion W X Y (Word.append Word.empty a) :=
      by rw [colimitComposition_fac]; rfl
    _ = (graphUnit W X ⊗ₘ 𝟙 (graph W a X Y)) ≫
        graphComposition W Word.empty a X X Y ≫
          (graphDiagram W X Y).map (eqToHom (Word.empty_append a)) ≫ graphInclusion W X Y a :=
      by rw [graphInclusion_naturality]
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun f => f ≫ graphInclusion W X Y a)
        (graphComposition_left_unit W a X Y)

lemma colimitComposition_right_unit_fac (a : Word) :
    (graphInclusion W X Y a ⊗ₘ colimitUnit W Y) ≫ colimitComposition W X Y Y =
      (ρ_ (graph W a X Y)).hom ≫ graphInclusion W X Y a := by
  calc
    _ = (𝟙 (graph W a X Y) ⊗ₘ graphUnit W Y) ≫
        (graphInclusion W X Y a ⊗ₘ graphInclusion W Y Y Word.empty) ≫
          colimitComposition W X Y Y := by
      rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
      rfl
    _ = (𝟙 (graph W a X Y) ⊗ₘ graphUnit W Y) ≫
        graphComposition W a Word.empty X Y Y ≫ graphInclusion W X Y (Word.append a Word.empty) :=
      by rw [colimitComposition_fac]; rfl
    _ = (𝟙 (graph W a X Y) ⊗ₘ graphUnit W Y) ≫
        graphComposition W a Word.empty X Y Y ≫
          (graphDiagram W X Y).map (eqToHom (Word.append_empty a)) ≫ graphInclusion W X Y a :=
      by rw [graphInclusion_naturality]
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun f => f ≫ graphInclusion W X Y a)
        (graphComposition_right_unit W a X Y)

/-- 元の空語の単位と実際の余極限上の合成の左単位則。 -/
lemma colimitComposition_left_unit :
    (colimitUnit W X ⊗ₘ 𝟙 (colimitGraph W X Y)) ≫ colimitComposition W X X Y =
      (λ_ (colimitGraph W X Y)).hom := by
  apply (cancel_epi (λ_ (colimitGraph W X Y)).inv).mp
  apply colimitGraph_hom_ext W X Y
  intro a
  rw [← Category.assoc, leftUnitor_inv_naturality, Category.assoc]
  simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp,
    Category.comp_id, colimitComposition_left_unit_fac, Iso.inv_hom_id_assoc, Iso.inv_hom_id]

/-- 元の空語の単位と実際の余極限上の合成の右単位則。 -/
lemma colimitComposition_right_unit :
    (𝟙 (colimitGraph W X Y) ⊗ₘ colimitUnit W Y) ≫ colimitComposition W X Y Y =
      (ρ_ (colimitGraph W X Y)).hom := by
  apply (cancel_epi (ρ_ (colimitGraph W X Y)).inv).mp
  apply colimitGraph_hom_ext W X Y
  intro a
  rw [← Category.assoc, rightUnitor_inv_naturality, Category.assoc]
  simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.id_comp,
    Category.comp_id, colimitComposition_right_unit_fac, Iso.inv_hom_id_assoc, Iso.inv_hom_id]

end SerrePositivity.EInfinity.Hammock
