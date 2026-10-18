module

public import SerrePositivity.KST.Comparison.SubdivisionNerveChains
public import SerrePositivity.KST.Comparison.FiniteChainGreatest
public import SerrePositivity.KST.Comparison.ExUnit

/-!
# 有限鎖の細分比較と最終頂点

概要：有限鎖の最大元への射を合成すると、既存の最終頂点から作った Ex の単位に一致する。
方針：各頂点で単調写像の像と有限鎖の最大元の交換を使う。
規約：Moss 2020 Proposition 21 の反復最終頂点の整合。
使われ方：horn 上で細分比較が所要の単位に一致すること。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite PartialOrder
open scoped Simplicial

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
theorem subdivisionNerveChains_naturality {P Q : Type u} [PartialOrder P] [PartialOrder Q]
    (f : P →o Q) :
    SSet.sd.map (nerveMap f.monotone.functor) ≫ subdivisionNerveChains Q =
      subdivisionNerveChains P ≫ nerveMap (NonemptyFiniteChains.orderHomMap f).monotone.functor := by
  apply (SSet.sdExAdjunction.homEquiv _ _).injective
  rw [SSet.sdExAdjunction.homEquiv_naturality_left,
    SSet.sdExAdjunction.homEquiv_naturality_right]
  simpa only [subdivisionNerveChains, Equiv.apply_symm_apply] using
    nerveChainsExUnit_naturality f

end SerrePositivity.KST.Comparison
