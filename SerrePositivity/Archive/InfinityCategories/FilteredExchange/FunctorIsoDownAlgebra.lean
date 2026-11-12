module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorSpaceDownNaturality
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerUnit
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FunctorIsoMapTransport

/-!
概要：指定関手同型の宇宙下降は、合成・逆・元の射による前後合成を保つ。
方針：関手空間の下降関手の mapIso とその自然性を使う。
規約：指定同型そのものの等式。使われ方：native cospan の四射の値比較の下降。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u v
open CategoryTheory MonoidalClosed SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 元の指定同型の合成は同じ指定順序で下降する。 -/
lemma functorIsoDown_trans {X Y : SSet.{u}} [Quasicategory Y] {f g h : X ⟶ Y}
    (e : FunctorIso ((SSet.uliftFunctor.{v, u}).map f) ((SSet.uliftFunctor.{v, u}).map g))
    (d : FunctorIso ((SSet.uliftFunctor.{v, u}).map g) ((SSet.uliftFunctor.{v, u}).map h)) :
    functorIsoDown (e ≪≫ d) = functorIsoDown e ≪≫ functorIsoDown d := by
  rw [functorIsoDown_eq_mapIso, functorIsoDown_eq_mapIso, functorIsoDown_eq_mapIso,
    Functor.mapIso_trans]

/-- 元の指定逆同型は下降した同じ同型の逆である。 -/
lemma functorIsoDown_symm {X Y : SSet.{u}} [Quasicategory Y] {f g : X ⟶ Y}
    (e : FunctorIso ((SSet.uliftFunctor.{v, u}).map f) ((SSet.uliftFunctor.{v, u}).map g)) :
    functorIsoDown e.symm = (functorIsoDown e).symm := by
  rw [functorIsoDown_eq_mapIso, functorIsoDown_eq_mapIso, Functor.mapIso_symm]

/-- 指定同型の下降は元の射の後合成と厳密に可換する。 -/
lemma functorIsoDown_postcomp {A X Y : SSet.{u}} [Quasicategory X] [Quasicategory Y]
    {f g : A ⟶ X}
    (e : FunctorIso ((SSet.uliftFunctor.{v, u}).map f) ((SSet.uliftFunctor.{v, u}).map g))
    (q : X ⟶ Y) :
    functorIsoDown (functorIsoOfEq (e.postcomp ((SSet.uliftFunctor.{v, u}).map q))
      ((SSet.uliftFunctor.{v, u}).map_comp f q).symm
      ((SSet.uliftFunctor.{v, u}).map_comp g q).symm) =
      (functorIsoDown e).postcomp q := by
  rw [functorIsoDown_eq_mapIso]
  apply eq_of_heq
  have hc := mapIso_functorIsoOfEq_heq (functorSpaceDown.{u, v} A Y)
    (e.postcomp ((SSet.uliftFunctor.{v, u}).map q))
    ((SSet.uliftFunctor.{v, u}).map_comp f q).symm
    ((SSet.uliftFunctor.{v, u}).map_comp g q).symm
  have hn := mapIso_heq_of_functor_eq_levels (functorSpaceDown_post.{u, v} (A := A) q).symm e
  have hh : HEq ((functorSpaceDown.{u, v} A Y).mapIso
      (e.postcomp ((SSet.uliftFunctor.{v, u}).map q))) ((functorIsoDown e).postcomp q) := by
    rw [functorIso_postcomp_eq_mapIso e,
      functorIso_postcomp_eq_mapIso (functorIsoDown e), functorIsoDown_eq_mapIso e]
    exact hn
  exact hc.trans hh

/-- 指定同型の下降は元の射の前合成と厳密に可換する。 -/
lemma functorIsoDown_precomp {A X Y : SSet.{u}} [Quasicategory Y] {f g : X ⟶ Y}
    (e : FunctorIso ((SSet.uliftFunctor.{v, u}).map f) ((SSet.uliftFunctor.{v, u}).map g))
    (q : A ⟶ X) :
    functorIsoDown (functorIsoOfEq (e.precomp ((SSet.uliftFunctor.{v, u}).map q))
      ((SSet.uliftFunctor.{v, u}).map_comp q f).symm
      ((SSet.uliftFunctor.{v, u}).map_comp q g).symm) =
      (functorIsoDown e).precomp q := by
  rw [functorIsoDown_eq_mapIso]
  apply eq_of_heq
  have hc := mapIso_functorIsoOfEq_heq (functorSpaceDown.{u, v} A Y)
    (e.precomp ((SSet.uliftFunctor.{v, u}).map q))
    ((SSet.uliftFunctor.{v, u}).map_comp q f).symm
    ((SSet.uliftFunctor.{v, u}).map_comp q g).symm
  have hn := mapIso_heq_of_functor_eq_levels (functorSpaceDown_pre.{u, v} (Y := Y) q).symm e
  have hh : HEq ((functorSpaceDown.{u, v} A Y).mapIso
      (e.precomp ((SSet.uliftFunctor.{v, u}).map q))) ((functorIsoDown e).precomp q) := by
    rw [functorIso_precomp_eq_mapIso e,
      functorIso_precomp_eq_mapIso (functorIsoDown e), functorIsoDown_eq_mapIso e]
    exact hn
  exact hc.trans hh

end SerrePositivity.InfinityCategories.F2
