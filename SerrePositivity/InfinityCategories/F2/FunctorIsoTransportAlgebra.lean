module

public import SerrePositivity.InfinityCategories.F2.FunctorEqIsoTransport

/-!
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
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：指定同型の端点の輸送は合成の比較を保つ。
方針：端点の等式を消去し標準同型を恒等同型に戻す。
規約：元の指定同型の値を保持する。
使われ方：引き戻し錐の二射影と指定 path の比較。 -/
lemma functorIso_postcomp_heq_of_heq {X Y : SSet.{u}} {f g f' g' : X ⟶ Y}
    (e : FunctorIso f g) (e' : FunctorIso f' g') (hf : f = f') (hg : g = g')
    (h : HEq e' e) {Z : SSet.{u}} (r : Y ⟶ Z) :
    HEq (e'.postcomp r) (e.postcomp r) := by
  subst f'
  subst g'
  cases eq_of_heq h
  rfl
/-- 概要：指定同型の端点の輸送は合成の比較を保つ。
方針：端点の等式を消去し標準同型を恒等同型に戻す。
規約：元の指定同型の値を保持する。
使われ方：引き戻し錐の二射影と指定 path の比較。 -/
lemma functorIso_source_transport_square {X Y : SSet.{u}} {f f' f'' g h : X ⟶ Y}
    (a : FunctorIso f g) (d : FunctorIso g h) (e : FunctorIso f' h) (n : FunctorIso f f')
    (hs : f = f'') (ht : f' = f'') (hn : IsFunctorEqIso n)
    (he : a ≪≫ d = n ≪≫ e) :
    functorIsoOfEq a hs rfl ≪≫ d = functorIsoOfEq e ht rfl := by
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
    (e : FunctorIso f g) (hf : f = f') (hg : g = g') :
    functorIsoOfEq e hf hg ≪≫ functorEqIso hg.symm = functorIsoOfEq e hf rfl := by
  subst f'
  subst g'
  exact Iso.trans_refl e

end SerrePositivity.InfinityCategories.F2
