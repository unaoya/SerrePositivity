module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.Equivalence

/-!
分割で生成：docstring を書き直すこと
概要：指定同型の合成正方形の端点の輸送。
方針：等式から来る同型を除去して同じ端点で比較する。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries

/-- 概要：指定同型の端点の輸送は合成の比較を保つ。
方針：端点の等式を消去し標準同型を恒等同型に戻す。
規約：元の指定同型の値を保持する。
使われ方：引き戻し錐の二射影と指定 path の比較。 -/
lemma functorIso_postcomp_heq_of_heq {X Y : SSet.{u}} {f g f' g' : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (e' : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' g') (hf : f = f') (hg : g = g')
    (h : HEq e' e) {Z : SSet.{u}} (r : Y ⟶ Z) :
    HEq (e'.postcomp r) (e.postcomp r) := by
  subst f'
  subst g'
  cases eq_of_heq h
  rfl
end SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries
