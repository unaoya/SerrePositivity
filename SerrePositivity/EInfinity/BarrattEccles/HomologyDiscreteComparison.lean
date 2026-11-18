module

public import SerrePositivity.EInfinity.BarrattEccles.HomologyCommutativeComparison
public import SerrePositivity.EInfinity.BarrattEccles.DiscreteAlgebra

/-!
# 離散 E 代数から取り出した積と単位の一致

概要：BF §1・BM §1 の離散 E 代数の H⁰ 演算の鎖射を元の積・単位に同定する。
方針：既存の対称モノイダル零次埋め込みで移した可換モノイドの比較を使う。
規約：実際の離散 E 代数関手と同じ複体・同じ演算を使う。
使われ方：H⁰ の環構造と離散可換代数の比較。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory

variable (A : Type u) [CommRing A]

/-- 概要：離散 E 代数から取り出した二入力射は元の零次複体の積（BF §1、BM §1）。
方針：可換モノイド複体からの制限についての一般比較を適用する。
規約：複体射の厳密な等式。
使われ方：H⁰ の積の離散可換代数との比較。 -/
lemma homologyBinary_discrete (B : CommAlgCat.{u} A) :
    homologyBinary ((discreteAlgebraFunctor A).obj B) =
      ((CochainComplex.singleFunctor (ModuleCat A) 0).mapCommMon.obj
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.moduleCommMonoid A B)).mon.mul := by
  let M := (CochainComplex.singleFunctor (ModuleCat A) 0).mapCommMon.obj
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.moduleCommMonoid A B)
  let := M.mon
  have := M.comm
  exact homologyBinary_commutative M.X

/-- 概要：離散 E 代数から取り出した零入力射は元の零次複体の単位（BF §1、BM §1）。
方針：可換モノイド複体からの制限についての零入力比較を適用する。
規約：実際の nullary 演算の等式。
使われ方：H⁰ の単位の離散可換代数との比較。 -/
lemma homologyNullary_discrete (B : CommAlgCat.{u} A) :
    homologyOperation ((discreteAlgebraFunctor A).obj B) 0 =
      ((CochainComplex.singleFunctor (ModuleCat A) 0).mapCommMon.obj
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.moduleCommMonoid A B)).mon.one := by
  let M := (CochainComplex.singleFunctor (ModuleCat A) 0).mapCommMon.obj
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.moduleCommMonoid A B)
  let := M.mon
  have := M.comm
  exact homologyNullary_commutative M.X

end SerrePositivity.EInfinity.BarrattEccles
