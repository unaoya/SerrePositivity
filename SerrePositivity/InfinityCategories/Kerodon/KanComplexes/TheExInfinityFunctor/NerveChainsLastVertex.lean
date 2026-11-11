module

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionNerveChains
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.FiniteChainGreatest
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.ExUnit
public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor.SubdivisionLastVertexMap

/-!
# 有限鎖の細分比較と最終頂点

概要：有限鎖の最大元への射を合成すると、既存の最終頂点から作った Ex の単位に一致する。
方針：各頂点で単調写像の像と有限鎖の最大元の交換を使う。
規約：Moss 2020 Proposition 21 の反復最終頂点の整合。
使われ方：horn 上で細分比較が所要の単位に一致すること。

対応節は Kerodon 3.3（Tag 00XF）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
open CategoryTheory Opposite PartialOrder
open scoped _root_.Simplicial

/--
概要：有限鎖への Ex の比較の後で最大元を取ると、Ex の単位になる。
方針：有限鎖の像の最大元を、元の最大元の像へ移す。
規約：Moss 2020 Proposition 21 の細分上の比較の整合。
使われ方：二重細分の horn の上での境界条件。
-/
theorem nerveChainsExUnit_lastVertex (P : Type u) [PartialOrder P] :
    nerveChainsExUnit P ≫ SSet.ex.map (nerveMap finiteChainGreatest.monotone.functor) =
      exUnitAt (nerve P) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro s
  apply ULift.ext
  apply NatTrans.ext
  funext d
  apply ConcreteCategory.hom_ext
  intro t
  apply nerve.ext_of_isThin
  funext i
  let a : NonemptyFiniteChains (ULift.{u} (Fin (n.unop.len + 1))) := t.obj i
  change finiteChainGreatest (a.map (nerveSimplexOrderHom n.unop s)) =
    s.obj (finiteChainMaximum a).down
  calc
    _ = (nerveSimplexOrderHom n.unop s) (finiteChainGreatest a) :=
      finiteChainGreatest_map (nerveSimplexOrderHom n.unop s) a
    _ = _ := congrArg (nerveSimplexOrderHom n.unop s) (finiteChainGreatest_eq_maximum a)

/--
概要：nerve の細分の比較は順序集合の単調写像に関して自然である。
方針：Ex への自然性を随伴同値の単射性で転置する。
規約：二重細分の horn の制限との整合。
使われ方：有限鎖の部分順序集合への比較の制限。
-/
@[reassoc] theorem subdivisionNerveChains_naturality {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) :
    SSet.sd.map (nerveMap f.monotone.functor) ≫ subdivisionNerveChains Q =
      subdivisionNerveChains P ≫ nerveMap (NonemptyFiniteChains.orderHomMap f).monotone.functor := by
  apply (SSet.sdExAdjunction.homEquiv _ _).injective
  rw [SSet.sdExAdjunction.homEquiv_naturality_left,
    SSet.sdExAdjunction.homEquiv_naturality_right]
  simpa only [subdivisionNerveChains, Equiv.apply_symm_apply] using
    nerveChainsExUnit_naturality f

/--
概要：nerve の細分比較から最大元への合成は、実際の最終頂点写像に一致する。
方針：Ex の単位との一致を随伴同値で転置する。
規約：二重細分の候補の境界条件を計算するための式。
使われ方：面の nerve 上の計算から細分された horn へ戻す。
-/
@[reassoc] theorem subdivisionNerveChains_lastVertex (P : Type u) [PartialOrder P] :
    subdivisionNerveChains P ≫ nerveMap finiteChainGreatest.monotone.functor =
      subdivisionLastVertexMap.app (nerve P) := by
  apply (SSet.sdExAdjunction.homEquiv _ _).injective
  rw [SSet.sdExAdjunction.homEquiv_naturality_right]
  simpa only [subdivisionNerveChains, subdivisionLastVertexMap, Functor.id_obj,
    Equiv.apply_symm_apply] using nerveChainsExUnit_lastVertex P

end SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheExInfinityFunctor
