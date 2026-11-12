module

public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FunctorIsoWhiskerCancellation

/-!
概要：元の同型の単位前合成と値射影による同定を、さらに元の始域射で制限する。
方針：実端点の表示変更と前後合成の結合則を任意の射に対して先に合成する。
規約：端点等式と指定値を保持。使われ方：一点輸送比較を最後辺の下側因子へ戻す。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 単位と値への作用で同定した同じ指定比較は、元の合成始域射による制限でも保たれる。 -/
lemma functorIso_unit_precomp_transport_heq {A B C D E : SSet.{u}}
    {p q : C ⟶ D} (e : FunctorIso p q) (v : D ⟶ E) (unit : B ⟶ C) (f : A ⟶ B)
    {p' q' : C ⟶ E} (hp : p ≫ v = p') (hq : q ≫ v = q')
    {l r : B ⟶ E} (d : FunctorIso l r)
    (hl : (unit ≫ p) ≫ v = l) (hr : (unit ≫ q) ≫ v = r)
    (he : HEq d ((e.precomp unit).postcomp v)) :
    HEq ((functorIsoOfEq (e.postcomp v) hp hq).precomp (f ≫ unit)) (d.precomp f) := by
  have hn := functorIso_precomp_heq_of_heq (e.postcomp v)
    (functorIsoOfEq (e.postcomp v) hp hq) hp hq (functorIsoOfEq_heq _ _ _) (f ≫ unit)
  have hd := (functorIso_precomp_heq_of_heq ((e.precomp unit).postcomp v)
    d hl hr he f).symm
  have hs : (e.postcomp v).precomp (f ≫ unit) =
      ((e.precomp unit).postcomp v).precomp f := by
    rw [functorIso_precomp_postcomp, functorIso_precomp_precomp]
  exact hn.trans ((heq_of_eq hs).trans hd)

end SerrePositivity.InfinityCategories.F2
