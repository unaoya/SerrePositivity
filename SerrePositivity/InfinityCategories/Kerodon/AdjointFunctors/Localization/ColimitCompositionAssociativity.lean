module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.GraphCompositionAssociativity
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TripleColimit

/-!
# 元の全語の余極限上の合成の結合則

概要：実際の三つの余極限の積上で、元の合成の結合則を証明する。
方針：外部積余錐の一意性を使い、元の全固定語の graph の結合則へ帰着する。
規約：元の合成・標準射を保持し、filtered 性や単体集合のモデル構造は使わない。
使われ方：hammock の実際の単体的豊穣圏。

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
  (X Y Z V : C)

lemma colimitComposition_assoc_left_fac (a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y a ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W Y Z b) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W Z V c) ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition W X Y Z ⊗ₘ 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W Z V)) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition W X Z V =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphComposition W a b X Y Z ⊗ₘ 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W c Z V)) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphComposition W (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b) c X Z V ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X V (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a b) c) := by
  rw [tensorHom_comp_tensorHom_assoc, Category.comp_id, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition_fac]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphPairing]
  rw [← Category.id_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W Z V c), ← tensorHom_comp_tensorHom_assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition_fac]
  rfl

lemma colimitComposition_assoc_right_fac (a b c : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word) :
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y a ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W Y Z b) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W Z V c) ≫
        (α_ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W Y Z) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W Z V)).hom ≫
          (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition W Y Z V) ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition W X Y V =
      (α_ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W a X Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W b Y Z) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W c Z V)).hom ≫
        (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graph W a X Y) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphComposition W b c Y Z V) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphComposition W a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append b c) X Y V ≫
            _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X V (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append b c)) := by
  rw [associator_naturality_assoc, tensorHom_comp_tensorHom_assoc, Category.comp_id,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition_fac]
  dsimp only [_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphPairing]
  rw [← Category.id_comp (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X Y a), ← tensorHom_comp_tensorHom_assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition_fac]
  rfl

/-- 元の三つの余極限の積からの、実際の合成の結合則。 -/
lemma colimitComposition_assoc :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition W X Y Z ⊗ₘ 𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W Z V)) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition W X Z V =
      (α_ (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W Y Z) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W Z V)).hom ≫
        (𝟙 (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitGraph W X Y) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition W Y Z V) ≫
          _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.colimitComposition W X Y V := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.tensorTriple_hom_ext W X Y Z V
  intro a b c
  rw [colimitComposition_assoc_left_fac, colimitComposition_assoc_right_fac]
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion_naturality W X V (eqToHom (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.append_assoc a b c))]
  simpa only [Category.assoc] using congrArg
    (fun f => f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphInclusion W X V (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append a (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.WordAppend.append b c)))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.graphComposition_assoc W a b c X Y Z V)

end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
