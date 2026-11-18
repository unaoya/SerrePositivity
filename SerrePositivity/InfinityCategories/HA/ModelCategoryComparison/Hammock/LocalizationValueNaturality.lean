module

public import SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.LocalizationValue
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValueComparison
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.StrictLocalization

/-!
# 元の通常の局所化評価の相対自然性

概要：同じ元の相対関手に沿う通常の局所化 Hom の値を、固定端点の移送まで照合する。
方針：元の strictLocalizationMap_fac を評価の可換正方形へ代入する。
規約：元の Q.map、元の相対関手、元の局所化の対象表示を保持する。
使われ方：元の自由解像の全作用素に自然な右比較。
-/

@[expose] public section
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
open _root_.CategoryTheory

variable {C D : Type u} [Category.{u} C] [Category.{u} D]
  {W : MorphismProperty C} [W.IsMultiplicative] {V : MorphismProperty D} [V.IsMultiplicative]
  (F : LocalizerMorphism W V) {w : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word} {X Y : C} {X' Y' : D}

omit [W.IsMultiplicative] [V.IsMultiplicative] in
lemma localization_value_relative (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) :
    HEq (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value V.Q V.Q_inverts (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeZigzagFunctor.obj F S))
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap F).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value W.Q W.Q_inverts S)) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.value_comparison F W.Q W.Q_inverts V.Q V.Q_inverts
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap F) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap_fac F) S

omit [W.IsMultiplicative] [V.IsMultiplicative] in
lemma fixedLocalizationObject_eq (hX : F.functor.obj X = X') :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap F).obj (W.Q.obj X) = V.Q.obj X' :=
  (CategoryTheory.Functor.congr_obj (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap_fac F) X).trans (congrArg V.Q.obj hX)

lemma localization_value_fixed (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y')
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag W w X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value V.Q V.Q_inverts ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor F hX hY).obj S) =
      eqToHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.fixedLocalizationObject_eq F hX).symm ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap F).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.ZigzagValuePath.value W.Q W.Q_inverts S) ≫
          eqToHom (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.fixedLocalizationObject_eq F hY) := by
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.value_fixed_comparison F W.Q W.Q_inverts V.Q V.Q_inverts
    (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap F) (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.strictLocalizationMap_fac F) hX hY S
  exact (conj_eqToHom_iff_heq _ _ (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.fixedLocalizationObject_eq F hX).symm
    (_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock.fixedLocalizationObject_eq F hY).symm).2 h

end SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.Hammock
