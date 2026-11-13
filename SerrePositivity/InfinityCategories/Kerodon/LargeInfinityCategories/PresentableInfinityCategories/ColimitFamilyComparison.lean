module

public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.NativeCoconeHomComparison
public import SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.FunctorHomVertexTransport
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.CoconeComparison.FunctorCoconeEvaluation

/-!
概要：普遍余錐族からの指定比較を全関手の比較とし、各点の余極限性で判定する。
方針：coslice の同じ射を全ての評価で使う。
規約：比較射を各点で選び直さない。
使われ方：有限余積の比較の可逆性を Yoneda 生成対象から広げる。

対応節は Kerodon 9.5（Tag 06NC）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories

/-- 概要：普遍余錐から元の指定余錐への全射を選ぶ。
方針：coslice のホモトピー圏で始対象からの一意な射を取る。
規約：一つの全射を全評価で共有する。
使われ方：有限余積の全関手の指定比較。 -/
def nativeColimitComparisonHom {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone c) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p) :
    (HomotopyCategory.mk c : hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p)) ⟶ HomotopyCategory.mk d :=
  hc.isInitialHo.to _

/-- 概要：全余錐比較の頂点射を元の二つの全関手間の Hom として表す。
方針：元の頂点射の両端だけを指定された表示へ輸送する。
規約：全余錐比較の射そのものを保持する。
使われ方：生成表示による全関手比較の検出。 -/
def colimitFamilyComparison {K A X : SSet.{u}} {p : K ⟶ (ihom A).obj X}
    {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p}
    (α : (HomotopyCategory.mk c : hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p)) ⟶ HomotopyCategory.mk d)
    {F G : A ⟶ X} (hF : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (hG : d.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G) :
    _root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.FunctorHom F G := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomOfVertexEq (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nativeCoconeHomApex α) hF hG

/-- 概要：各点で両余錐が普遍なら同じ全比較はその点で可逆。
方針：評価した coslice 射の頂点の可逆性を表示の輸送へ戻す。
規約：元の全比較を評価する。
使われ方：Yoneda 像上での有限余積比較。 -/
lemma colimitFamilyComparison_evaluate_isIso {K A X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ (ihom A).obj X} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p}
    (α : (HomotopyCategory.mk c : hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p)) ⟶ HomotopyCategory.mk d)
    {F G : A ⟶ X} (hF : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (hG : d.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)
    (a : A _⦋0⦌) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.evaluateFunctorCocone c a))
    (hd : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.evaluateFunctorCocone d a)) :
    IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (colimitFamilyComparison α hF hG) a) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomOfVertexEq_evaluate_isIso_iff _ hF hG a).mpr
  have h := _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nativeCoconeHomApex_isIso hc hd (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nativeCoconeHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a) α)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nativeCoconeHomApex_postcomp] at h
  exact h

/-- 概要：各点で普遍な始域の余錐からの全比較が可逆なら標的の同じ余錐も普遍。
方針：評価の可逆性を同じ coslice の全射へ反映する。
規約：元の標的全余錐を保つ。
使われ方：全比較の検出から有限余積保存へ戻す。 -/
lemma isColimitCone_of_colimitFamilyComparison_evaluate_isIso
    {K A X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ (ihom A).obj X} {c d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone p}
    (α : (HomotopyCategory.mk c : hoFunctor.obj (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnder p)) ⟶ HomotopyCategory.mk d)
    {F G : A ⟶ X} (hF : c.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex F) (hG : d.vertex = _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex G)
    (a : A _⦋0⦌) (hc : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.evaluateFunctorCocone c a))
    (h : IsIso (_root_.SerrePositivity.InfinityCategories.Project.LocalizationAndKanExtensionAuxiliaries.FunctorCategories.functorHomEvaluate (colimitFamilyComparison α hF hG) a)) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.IsColimitCone (_root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.evaluateFunctorCocone d a) := by
  have hi := (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.functorHomOfVertexEq_evaluate_isIso_iff (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nativeCoconeHomApex α) hF hG a).mp h
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.isColimitCone_of_nativeCoconeHomApex_isIso hc
    (_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nativeCoconeHomPostcomp (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt a) α)
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories.nativeCoconeHomApex_postcomp]
  exact hi

end SerrePositivity.InfinityCategories.Kerodon.LargeInfinityCategories.PresentableInfinityCategories
