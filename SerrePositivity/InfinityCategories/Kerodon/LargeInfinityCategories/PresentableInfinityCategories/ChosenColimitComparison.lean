module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ColimitFamilyComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.ChosenColimitImageCocone

/-!
概要：選んだ余極限関手と任意の関手の間の余極限比較を全関手の Hom として構成する。
方針：像の図式族の普遍余錐から元の余錐族の像への一つの全射を取る。
規約：各点で比較を選び直さない。
使われ方：有限余積保存を Yoneda 像から全対象へ移す。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
variable {K X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
  (hX : ∀ p : K ⟶ X, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p) (hY : ∀ p : K ⟶ Y, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.HasColimit p) (q : X ⟶ Y)

/-- 概要：元の普遍余錐族の像への指定した全余錐比較。
方針：像の全図式の普遍余錐から始対象の一意な射を取る。
規約：全ての評価で一つの同じ射を使う。
使われ方：有限余積関手の全比較。 -/
def chosenColimitComparisonHom :
    (HomotopyCategory.mk
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitParameterCocone hY ((𝟙 ((ihom K).obj X)) ≫ (ihom K).map q)) :
      hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv _ _ _
        ((𝟙 ((ihom K).obj X)) ≫ (ihom K).map q)))) ⟶
    HomotopyCategory.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitImageCocone hX (𝟙 ((ihom K).obj X)) q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nativeColimitComparisonHom _ (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitParameterCocone_isColimit hY _) _

/-- 概要：元の二つの全関手の間の指定した余極限比較。
方針：全余錐比較を頂点で射影し、同じ余極限関手の表示へ戻す。
規約：元の全比較を保持する。
使われ方：生成対象上の比較の可逆性の検出。 -/
def chosenColimitComparison :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom ((ihom K).map q ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.chosenColimitFunctor K Y hY)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.chosenColimitFunctor K X hX ≫ q) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.colimitFamilyComparison (chosenColimitComparisonHom hX hY q)
    (by simpa only [Category.id_comp] using
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitParameterCocone_vertex hY ((𝟙 ((ihom K).obj X)) ≫ (ihom K).map q))
    (by simpa only [Category.id_comp] using
      _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitImageCocone_vertex hX (𝟙 ((ihom K).obj X)) q)

/-- 概要：指定した図式で余錐族の像が普遍なら、元の全比較はその図式で可逆。
方針：同じ全比較を評価し、二つの普遍余錐の比較を使う。
規約：元の全関手比較自身について結論する。
使われ方：Yoneda 像上の有限余積比較の入口。 -/
lemma chosenColimitComparison_evaluate_isIso (a : ((ihom K).obj X) _⦋0⦌)
    (h : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.evaluateFunctorCocone
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitImageCocone hX (𝟙 ((ihom K).obj X)) q) a)) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (chosenColimitComparison hX hY q) a) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.colimitFamilyComparison_evaluate_isIso _ _ _ a
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitParameterCocone_isPointwiseColimit hY
      ((𝟙 ((ihom K).obj X)) ≫ (ihom K).map q) a) h

/-- 概要：全比較が指定した図式で可逆なら元の余錐族の像はそこで普遍。
方針：同じ全余錐比較の頂点での可逆性を元の余錐へ反映する。
規約：指定した像の全余錐を保持する。
使われ方：有限余積保存の十分条件。 -/
lemma chosenColimitImageCocone_evaluate_isColimit (a : ((ihom K).obj X) _⦋0⦌)
    (h : IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (chosenColimitComparison hX hY q) a)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.evaluateFunctorCocone
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitImageCocone hX (𝟙 ((ihom K).obj X)) q) a) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isColimitCone_of_colimitFamilyComparison_evaluate_isIso _ _ _ a
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.chosenColimitParameterCocone_isPointwiseColimit hY
      ((𝟙 ((ihom K).obj X)) ≫ (ihom K).map q) a) h

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
