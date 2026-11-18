module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumnForwardBackwardData
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.FirstColumnForwardForwardRightCoherence
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedCoefficientCoherence

/-!
# 元の混合二方向の係数写像全体の恒等・合成

概要：底と両係数を持つ元の Data 写像全体の関手則を証明する。
方針：通常 Hom と残りの語の既存の係数則を積関手へ渡す。
規約：両端の表示を保持し、元の写像全体の等式を結論する。
使われ方：全図式と元の augmentation の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn
open _root_.CategoryTheory _root_.Opposite
variable {C D E : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} (w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word)
lemma forwardBackwardDataMap_id (F : C ⟶ C) (h : F = 𝟙 C) (X Y : C.category)
    (hX : F.functor.obj X = X) (hY : F.functor.obj Y = Y) :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.forwardBackwardDataMap w F hX hY = 𝟙 (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.forwardBackwardData C w X Y) := by
  cases h
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.hom_ext _ _ rfl (heq_of_eq rfl) ?_
  apply heq_of_eq
  ext Z
  change WideSubcategory C.weakEquivalences at Z
  have he := eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardRightMap_id_heq w (𝟙 C) rfl X Y hX Z)
  have ht := eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedFunctor_id_toCatHom_heq
    (w := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) (LocalizerMorphism.id C.weakEquivalences) rfl Z.obj Y hY)
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardRightMap (Y := Y) (Y' := Y) w (𝟙 C) hX).app Z).toFunctor.prod
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor (w := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w)
        (LocalizerMorphism.id C.weakEquivalences) rfl hY) = 𝟭 _
  have htF := congrArg Cat.Hom.toFunctor ht
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor (w := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w)
    (LocalizerMorphism.id C.weakEquivalences) rfl hY = _ at htF
  rw [he, htF]
  rfl
lemma forwardBackwardDataMap_comp (F : C ⟶ D) (G : D ⟶ E) (H : C ⟶ E)
    (h : H = F ≫ G) (X Y : C.category) (X' Y' : D.category) (X'' Y'' : E.category)
    (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y')
    (hX' : G.functor.obj X' = X'') (hY' : G.functor.obj Y' = Y'')
    (hXH : H.functor.obj X = X'') (hYH : H.functor.obj Y = Y'') :
    _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.forwardBackwardDataMap w H hXH hYH =
      _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.forwardBackwardDataMap w F hX hY ≫ _root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn.forwardBackwardDataMap w G hX' hY' := by
  cases h
  refine _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.TwoSidedDiagram.hom_ext _ _ rfl (heq_of_eq rfl) ?_
  apply heq_of_eq
  ext Z
  change WideSubcategory C.weakEquivalences at Z
  have he := eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardRightMap_comp_heq w F G (F ≫ G) rfl
    X Y X' Y' X'' Y'' hX hX' hXH Z)
  have ht := eq_of_heq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.fixedFunctor_comp_toCatHom_heq
    (w := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) F G (F ≫ G) rfl Z.obj Y Y' Y'' hY hY' hYH)
  change ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.forwardForwardRightMap (Y := Y) (Y' := Y'') w (F ≫ G) hXH).app Z).toFunctor.prod
      (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor (w := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) (F ≫ G) rfl hYH) = _
  have htF := congrArg Cat.Hom.toFunctor ht
  change _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor (w := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.cons .backward w) (F ≫ G) rfl hYH = _ at htF
  rw [he, htF]
  rfl
end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.FirstColumn
