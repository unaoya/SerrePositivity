module

public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.SingleZigzagRelativeValue
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.BackwardZigzagNativeDiscrete
public import SerrePositivity.InfinityCategories.F1B.Localization.DwyerKan.RelativeMarkedCategory

/-!
# 元の指定 Hom への評価と相対自然性

概要：同じ始終点の元の単一列を評価する。
方針：端点移送と離散圏の nerve の同型を使う。
規約：モデル構造を要求しない。
使われ方：DK5.7の単一列の比較。
-/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.EInfinity.Hammock.BackwardZigzag
open CategoryTheory SimplicialLocalization
variable {C D : RelativeCategory.{u}} {X Y : C.category} {X' Y' : D.category}
 (F : C ⟶ D) (hX : F.functor.obj X = X') (hY : F.functor.obj Y = Y')
lemma nativeValue_relative
    (S : Zigzag C.weakEquivalences (Word.single .backward) X Y) :
    markedHomEquiv (value ((Zigzag.Relative.fixedFunctor F hX hY).obj S)) =
      eqToHom (congrArg (fun Z => (⟨Z⟩ : WideSubcategory D.weakEquivalences)) hY).symm ≫
        (markedCategoryMap F).map (markedHomEquiv (value S)) ≫
      eqToHom (congrArg (fun Z => (⟨Z⟩ : WideSubcategory D.weakEquivalences)) hX) := by
  apply WideSubcategory.hom_ext
  have hx : (eqToHom (congrArg (fun Z =>
      (⟨Z⟩ : WideSubcategory D.weakEquivalences)) hX)).hom = eqToHom hX := by
    exact eqToHom_map (wideSubcategoryInclusion D.weakEquivalences) _
  have hy : (eqToHom (congrArg (fun Z =>
      (⟨Z⟩ : WideSubcategory D.weakEquivalences)) hY).symm).hom = eqToHom hY.symm := by
    exact eqToHom_map (wideSubcategoryInclusion D.weakEquivalences) _
  simpa only [WideSubcategory.comp_def, markedHomEquiv, markedCategoryMap,
    Equiv.coe_fn_mk, hx, hy] using value_relative F hX hY S
end SerrePositivity.EInfinity.Hammock.BackwardZigzag
