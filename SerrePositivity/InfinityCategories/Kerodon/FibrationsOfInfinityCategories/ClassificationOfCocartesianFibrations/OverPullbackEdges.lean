module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.PullbackEdgeReflection
public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.OverPullbackColimits

/-!
概要：底上の図式の自然な pullback 関手は、各底変換の元の cocartesian 辺を保つ。
方針：各辺を固定した全空間への第二射影で検出し、その射影の自然性を使う。
規約：可変の底は任意の単体集合でよく、quasicategory 性を要求しない。
使われ方：セルへの引き戻しで指定辺を保つ制限図式を作る。

対応節は Kerodon 5.6（Tag 027M）。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations

/-- 底を第一因子とする元の pullback の cocartesian 性も、固定した全空間への射影で検出する。 -/
lemma isCocartesianEdge_overPullback_iff {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] (a : Over B)
    (e : (pullback a.hom p) _⦋1⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (pullback.fst a.hom p) e ↔
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge p ((pullback.snd a.hom p).app (Opposite.op ⦋1⦌) e) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations.isCocartesianEdge_isPullback_iff p (IsPullback.of_hasPullback a.hom p).flip e

/-- 底上の任意の射による引き戻しの誘導射は、各底変換の cocartesian 辺を保つ。 -/
lemma isCocartesianEdge_overPullback_map {E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.CocartesianFibration p] {a b : Over B} (f : a ⟶ b)
    (e : (pullback a.hom p) _⦋1⦌) (he : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (pullback.fst a.hom p) e) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.IsCocartesianEdge (pullback.fst b.hom p)
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map f).app (Opposite.op ⦋1⦌) e) := by
  apply (isCocartesianEdge_overPullback_iff p b _).mpr
  have h := (isCocartesianEdge_overPullback_iff p a e).mp he
  have hn : (pullback.snd b.hom p).app (Opposite.op ⦋1⦌)
      (((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying p).map f).app (Opposite.op ⦋1⦌) e) =
      (pullback.snd a.hom p).app (Opposite.op ⦋1⦌) e :=
    congrArg (fun k ↦ k.app (Opposite.op ⦋1⦌) e) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying_map_snd p f)
  rwa [hn]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.ClassificationOfCocartesianFibrations
