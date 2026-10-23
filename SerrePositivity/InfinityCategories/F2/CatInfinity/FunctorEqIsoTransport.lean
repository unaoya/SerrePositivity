module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorEqIsoAlgebra

/-!
概要：指定同型の端点の輸送と標準同型の判定。
方針：端点の等式を消去して元の指定同型へ戻す。
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

/-- 概要：指定同型の端点の輸送と標準同型の判定。
方針：端点の等式を消去して元の指定同型へ戻す。
規約：元の指定同型を保持する。
使われ方：切断上の指定 path の同型の簡約。 -/
lemma functorIso_precomp_heq_of_heq {X Y : SSet.{u}} {f g f' g' : X ⟶ Y}
    (e : FunctorIso f g) (e' : FunctorIso f' g') (hf : f = f') (hg : g = g')
    (h : HEq e' e) {D : SSet.{u}} (r : D ⟶ X) :
    HEq (e'.precomp r) (e.precomp r) := by
  subst f'
  subst g'
  cases eq_of_heq h
  rfl
/-- 概要：指定同型の端点の輸送と標準同型の判定。
方針：端点の等式を消去して元の指定同型へ戻す。
規約：元の指定同型を保持する。
使われ方：切断上の指定 path の同型の簡約。 -/
lemma IsFunctorEqIso.of_heq {X Y : SSet.{u}} {f g f' g' : X ⟶ Y}
    {e : FunctorIso f g} {e' : FunctorIso f' g'} (he : IsFunctorEqIso e)
    (hf : f = f') (hg : g = g') (h : HEq e' e) : IsFunctorEqIso e' := by
  subst f'
  subst g'
  cases eq_of_heq h
  exact he

end SerrePositivity.InfinityCategories.F2
