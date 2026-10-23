module

public import SerrePositivity.InfinityCategories.F2.CatInfinity.FunctorEqIso

/-!
概要：等式からの同型を含む可換正方形の端点の正規化。
方針：端点の等式を消去して指定同型を輸送する。
規約：指定された三角形と同型の値を保持する。
使われ方：引き戻し錐と指定 path の比較を簡約する。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory Limits MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：等式からの同型を含む可換正方形の端点の正規化。
方針：端点の等式を消去して指定同型を輸送する。
規約：元の指定同型の値を保持する。
使われ方：二射影の指定比較と指定 path の整合。 -/
lemma functorIso_transport_square {X Y : SSet.{u}} {f g g' h h' : X ⟶ Y}
    (a : FunctorIso f g) (e : FunctorIso g' h') (r : FunctorIso f h)
    (hs : g' = g) (ht : h = h')
    (ha : a ≪≫ functorEqIso hs.symm ≪≫ e = r ≪≫ functorEqIso ht) :
    a ≪≫ functorIsoOfEq e hs ht.symm = r := by
  subst g'
  subst h'
  simpa only [functorEqIso, functorIsoOfEq, Iso.trans_refl, Iso.refl_trans] using ha

end SerrePositivity.InfinityCategories.F2
