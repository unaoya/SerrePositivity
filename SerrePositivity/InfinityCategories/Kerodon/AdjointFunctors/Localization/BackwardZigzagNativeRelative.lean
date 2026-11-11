module

public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.SingleZigzagRelativeValue
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagNativeDiscrete
public import SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeMarkedCategory

/-!
# 元の指定 Hom への評価と相対自然性

概要：同じ始終点の元の単一列を評価する。
方針：端点移送と離散圏の nerve の同型を使う。
規約：モデル構造を要求しない。
使われ方：DK5.7の単一列の比較。

対応節は Kerodon 6.3（Tag 01M4）。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
open CategoryTheory
variable {C D : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u}} {X Y : C.category} {X' Y' : D.category}
 (F : C ⟶ D) (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y')
lemma nativeValue_relative
    (S : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Zigzag C.weakEquivalences (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.Word.single .backward) X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedHomEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagDiscrete.value ((_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeFixedZigzagFunctor.fixedFunctor F hX hY).obj S)) =
      eqToHom (congrArg (fun Z => (⟨Z⟩ : WideSubcategory D.weakEquivalences)) hY).symm ≫
        (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap F).map (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedHomEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzagDiscrete.value S)) ≫
      eqToHom (congrArg (fun Z => (⟨Z⟩ : WideSubcategory D.weakEquivalences)) hX) := by
  apply WideSubcategory.hom_ext
  have hx : (eqToHom (congrArg (fun Z =>
      (⟨Z⟩ : WideSubcategory D.weakEquivalences)) hX)).hom = eqToHom hX := by
    exact eqToHom_map (wideSubcategoryInclusion D.weakEquivalences) _
  have hy : (eqToHom (congrArg (fun Z =>
      (⟨Z⟩ : WideSubcategory D.weakEquivalences)) hY).symm).hom = eqToHom hY.symm := by
    exact eqToHom_map (wideSubcategoryInclusion D.weakEquivalences) _
  simpa only [WideSubcategory.comp_def, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedHomEquiv, _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.markedCategoryMap,
    Equiv.coe_fn_mk, hx, hy] using _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.BackwardZigzag.value_relative F hX hY S
end SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization
