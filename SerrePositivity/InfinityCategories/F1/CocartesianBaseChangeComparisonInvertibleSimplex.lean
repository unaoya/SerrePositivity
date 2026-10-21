module

public import SerrePositivity.InfinityCategories.F1.InvertibleTriangleCancellation
public import SerrePositivity.InfinityCategories.F1.CocartesianBaseChangeJointComparisonIso

/-!
概要：元の比較辺の可逆性を、同じ一単体の標準端点表示で使う。
方針：元の辺を変更せず、その同じ一単体へ可逆性を移す。
規約：元の全 fibration の比較辺そのものを保持する。
使われ方：大域比較三角形の三辺の可逆性の検査を小さい補題へ分ける。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories

/-- 元の大域比較辺は、同じ一単体の標準端点表示でも可逆。 -/
lemma cocartesianBaseChangeJointComparisonEdge_simplex_isInvertible
    {C D : Type u} [Category.{u} C] [Category.{u} D] (k : D ⥤ C) :
    IsInvertibleEdge (edgeOfSimplex (cocartesianBaseChangeJointComparisonEdge k).edge) :=
  isInvertibleEdge_edgeOfSimplex
    (X := (ihom (CocartesianFibrationInfinity (nerve C))).obj
      (CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve D))))
    (cocartesianBaseChangeJointComparisonEdge k)
    (cocartesianBaseChangeJointComparisonEdge_isInvertible k)

end SerrePositivity.InfinityCategories
