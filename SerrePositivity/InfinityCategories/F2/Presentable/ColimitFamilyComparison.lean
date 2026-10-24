module

public import SerrePositivity.InfinityCategories.F2.Presentable.NativeCoconeHomComparison
public import SerrePositivity.InfinityCategories.F2.Presentable.FunctorHomVertexTransport
public import SerrePositivity.InfinityCategories.F2.FilteredExchange.FunctorCoconeEvaluation

/-!
概要：普遍余錐族からの指定比較を全関手の比較とし、各点の余極限性で判定する。
方針：coslice の同じ射を全ての評価で使う。
規約：比較射を各点で選び直さない。
使われ方：有限余積の比較の可逆性を Yoneda 生成対象から広げる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Presentable

/-- 概要：普遍余錐から元の指定余錐への全射を選ぶ。
方針：coslice のホモトピー圏で始対象からの一意な射を取る。
規約：一つの全射を全評価で共有する。
使われ方：有限余積の全関手の指定比較。 -/
def nativeColimitComparisonHom {K X : SSet.{u}} [Quasicategory X] {p : K ⟶ X}
    (c : JoinCocone p) (hc : IsColimitCone c) (d : JoinCocone p) :
    (HomotopyCategory.mk c : hoFunctor.obj (sliceUnder p)) ⟶ HomotopyCategory.mk d :=
  hc.isInitialHo.to _

/-- 概要：全余錐比較の頂点射を元の二つの全関手間の Hom として表す。
方針：元の頂点射の両端だけを指定された表示へ輸送する。
規約：全余錐比較の射そのものを保持する。
使われ方：生成表示による全関手比較の検出。 -/
def colimitFamilyComparison {K A X : SSet.{u}} {p : K ⟶ (ihom A).obj X}
    {c d : JoinCocone p}
    (α : (HomotopyCategory.mk c : hoFunctor.obj (sliceUnder p)) ⟶ HomotopyCategory.mk d)
    {F G : A ⟶ X} (hF : c.vertex = functorVertex F) (hG : d.vertex = functorVertex G) :
    FunctorHom F G := functorHomOfVertexEq (nativeCoconeHomApex α) hF hG

/-- 概要：各点で両余錐が普遍なら同じ全比較はその点で可逆。
方針：評価した coslice 射の頂点の可逆性を表示の輸送へ戻す。
規約：元の全比較を評価する。
使われ方：Yoneda 像上での有限余積比較。 -/
lemma colimitFamilyComparison_evaluate_isIso {K A X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ (ihom A).obj X} {c d : JoinCocone p}
    (α : (HomotopyCategory.mk c : hoFunctor.obj (sliceUnder p)) ⟶ HomotopyCategory.mk d)
    {F G : A ⟶ X} (hF : c.vertex = functorVertex F) (hG : d.vertex = functorVertex G)
    (a : A _⦋0⦌) (hc : IsColimitCone (evaluateFunctorCocone c a))
    (hd : IsColimitCone (evaluateFunctorCocone d a)) :
    IsIso (functorHomEvaluate (colimitFamilyComparison α hF hG) a) := by
  apply (functorHomOfVertexEq_evaluate_isIso_iff _ hF hG a).mpr
  have h := nativeCoconeHomApex_isIso hc hd (nativeCoconeHomPostcomp (evaluateFunctorAt a) α)
  rw [nativeCoconeHomApex_postcomp] at h
  exact h

/-- 概要：各点で普遍な始域の余錐からの全比較が可逆なら標的の同じ余錐も普遍。
方針：評価の可逆性を同じ coslice の全射へ反映する。
規約：元の標的全余錐を保つ。
使われ方：全比較の検出から有限余積保存へ戻す。 -/
lemma isColimitCone_of_colimitFamilyComparison_evaluate_isIso
    {K A X : SSet.{u}} [Quasicategory X]
    {p : K ⟶ (ihom A).obj X} {c d : JoinCocone p}
    (α : (HomotopyCategory.mk c : hoFunctor.obj (sliceUnder p)) ⟶ HomotopyCategory.mk d)
    {F G : A ⟶ X} (hF : c.vertex = functorVertex F) (hG : d.vertex = functorVertex G)
    (a : A _⦋0⦌) (hc : IsColimitCone (evaluateFunctorCocone c a))
    (h : IsIso (functorHomEvaluate (colimitFamilyComparison α hF hG) a)) :
    IsColimitCone (evaluateFunctorCocone d a) := by
  have hi := (functorHomOfVertexEq_evaluate_isIso_iff (nativeCoconeHomApex α) hF hG a).mp h
  apply isColimitCone_of_nativeCoconeHomApex_isIso hc
    (nativeCoconeHomPostcomp (evaluateFunctorAt a) α)
  rw [nativeCoconeHomApex_postcomp]
  exact hi

end SerrePositivity.InfinityCategories.F2.Presentable
