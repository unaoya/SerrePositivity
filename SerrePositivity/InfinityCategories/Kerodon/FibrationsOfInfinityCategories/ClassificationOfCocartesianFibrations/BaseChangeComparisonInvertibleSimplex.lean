module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.InvertibleTriangleCancellation
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.BaseChangeJointComparisonIso

/-!
概要：元の比較辺の可逆性を、同じ一単体の標準端点表示で使う。
方針：元の辺を変更せず、その同じ一単体へ可逆性を移す。
規約：元の全 fibration の比較辺そのものを保持する。
使われ方：大域比較三角形の三辺の可逆性の検査を小さい補題へ分ける。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 元の大域比較辺は、同じ一単体の標準端点表示でも可逆。 -/
lemma cocartesianBaseChangeJointComparisonEdge_simplex_isInvertible
    {C D : Type u} [Category.{u} C] [Category.{u} D] (k : D ⥤ C) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeJointComparisonEdge k).edge) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.isInvertibleEdge_edgeOfSimplex
    (X := (ihom (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.CocartesianFibrationInfinity (nerve C))).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.CatInfinityFunctor ((SSet.uliftFunctor.{u + 1, u}).obj (nerve D))))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeJointComparisonEdge k)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.cocartesianBaseChangeJointComparisonEdge_isInvertible k)

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
