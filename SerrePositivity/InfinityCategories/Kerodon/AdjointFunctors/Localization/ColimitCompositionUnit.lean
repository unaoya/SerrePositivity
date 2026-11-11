module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ColimitComposition
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GraphCompositionUnit

/-!
# 元の全語の余極限上の合成の左右単位則

概要：同じ元の空語の単位と二つの余極限の積からの合成は、左右の単位則を満たす。
方針：全固定語で元の合成を回収し、語の単位遷移の余錐条件から余極限へ降下する。
規約：添字圏の filtered 性・単体集合のモデル構造は要求しない。
使われ方：hammock の実際の豊穣圏の単位公理。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
universe u v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory MonoidalCategory

variable {C : Type u} [Category.{v} C] (W : MorphismProperty C) [W.IsMultiplicative]
  (X Y : C)

lemma colimitComposition_left_unit_fac (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit W X ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y a) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition W X X Y =
      (λ_ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W a X Y)).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y a := by
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphUnit W X ⊗ₘ 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W a X Y)) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X X _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y a) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition W X X Y := by
      rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
      rfl
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphUnit W X ⊗ₘ 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W a X Y)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphComposition W _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty a X X Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty a) :=
      by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition_fac]; rfl
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphUnit W X ⊗ₘ 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W a X Y)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphComposition W _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty a X X Y ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map (eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit.empty_append a)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y a :=
      by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion_naturality]
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun f => f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y a)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphComposition_left_unit W a X Y)

lemma colimitComposition_right_unit_fac (a : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y a ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit W Y) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition W X Y Y =
      (ρ_ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W a X Y)).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y a := by
  calc
    _ = (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W a X Y) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphUnit W Y) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y a ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W Y Y _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition W X Y Y := by
      rw [← Category.assoc, tensorHom_comp_tensorHom, Category.id_comp]
      rfl
    _ = (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W a X Y) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphUnit W Y) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphComposition W a _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty X Y Y ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty) :=
      by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition_fac]; rfl
    _ = (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W a X Y) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphUnit W Y) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphComposition W a _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.empty X Y Y ≫
          (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Diagram.graphDiagram W X Y).map (eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordUnit.append_empty a)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y a :=
      by rw [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion_naturality]
    _ = _ := by
      simpa only [Category.assoc] using congrArg (fun f => f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y a)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphComposition_right_unit W a X Y)

/-- 元の空語の単位と実際の余極限上の合成の左単位則。 -/
lemma colimitComposition_left_unit :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit W X ⊗ₘ 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition W X X Y =
      (λ_ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y)).hom := by
  apply (cancel_epi (λ_ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y)).inv).mp
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph_hom_ext W X Y
  intro a
  rw [← Category.assoc, leftUnitor_inv_naturality, Category.assoc]
  simp only [← id_tensorHom, tensorHom_comp_tensorHom_assoc, Category.id_comp,
    Category.comp_id, colimitComposition_left_unit_fac, Iso.inv_hom_id_assoc, Iso.inv_hom_id]

/-- 元の空語の単位と実際の余極限上の合成の右単位則。 -/
lemma colimitComposition_right_unit :
    (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitUnit W Y) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition W X Y Y =
      (ρ_ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y)).hom := by
  apply (cancel_epi (ρ_ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y)).inv).mp
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph_hom_ext W X Y
  intro a
  rw [← Category.assoc, rightUnitor_inv_naturality, Category.assoc]
  simp only [← tensorHom_id, tensorHom_comp_tensorHom_assoc, Category.id_comp,
    Category.comp_id, colimitComposition_right_unit_fac, Iso.inv_hom_id_assoc, Iso.inv_hom_id]

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
