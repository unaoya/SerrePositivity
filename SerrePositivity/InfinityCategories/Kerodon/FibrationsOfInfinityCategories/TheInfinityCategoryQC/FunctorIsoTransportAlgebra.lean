module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.FunctorEqIsoAlgebra

/-!
概要：指定同型の合成正方形の端点の輸送。
方針：等式から来る同型を除去して同じ端点で比較する。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。

対応節は Kerodon 5.5（Tag 01YV）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC

/-- 概要：指定同型の端点の輸送は合成の比較を保つ。
方針：端点の等式を消去し標準同型を恒等同型に戻す。
規約：元の指定同型の値を保持する。
使われ方：引き戻し錐の二射影と指定 path の比較。 -/
lemma functorIso_source_transport_square {X Y : SSet.{u}} {f f' f'' g h : X ⟶ Y}
    (a : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso g h) (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f' h) (n : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f f')
    (hs : f = f'') (ht : f' = f'') (hn : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.IsFunctorEqIso n)
    (he : a ≪≫ d = n ≪≫ e) :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq a hs rfl ≪≫ d = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e ht rfl := by
  subst f
  subst f'
  have hn' : n = Iso.refl _ := hn.eq rfl
  rw [hn', Iso.refl_trans] at he
  exact he
/-- 概要：指定同型の端点の輸送は合成の比較を保つ。
方針：端点の等式を消去し標準同型を恒等同型に戻す。
規約：元の指定同型の値を保持する。
使われ方：引き戻し錐の二射影と指定 path の比較。 -/
lemma functorIsoOfEq_trans_eqIso {X Y : SSet.{u}} {f g f' g' : X ⟶ Y}
    (e : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso f g) (hf : f = f') (hg : g = g') :
    _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e hf hg ≪≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.functorEqIso hg.symm = _root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.functorIsoOfEq e hf rfl := by
  subst f'
  subst g'
  exact Iso.trans_refl e

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC
