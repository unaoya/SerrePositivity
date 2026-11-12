module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinLeftFunctor
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.JoinPushout
public import Mathlib.CategoryTheory.Adhesive.Basic

/-!
概要：relative join の左因子の単射に沿う pushout の保存。
方針：通常の join の pushout と比較の pullback 四角形から、van Kampen の貼り合わせを使う。
規約：通常の単体集合の pushout の主張であり、空間の ∞ 余極限を主張しない。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、始域の単体の貼り合わせによる比較の帰納法。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：共通の底上で左因子の単射に沿う pushout を relative join が保つ。
方針：通常の join の pushout の四辺の逆像を relative join と表示し、van Kampen 性を使う。
規約：単射性は左上から右上への射の左成分だけに要求する。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、境界から単体を追加する段階での relative join の分解。 -/
lemma relativeJoin_left_isPushout {Y S : SSet.{u}} (g : Y ⟶ S)
    {A B C D : Over S} {u : A ⟶ B} {v : A ⟶ C} {r : B ⟶ D} {s : C ⟶ D}
    [Mono u.left] (hp : IsPushout u.left v.left r.left s.left) :
    IsPushout ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLeftFunctor g).map u) ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLeftFunctor g).map v)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLeftFunctor g).map r) ((_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLeftFunctor g).map s) := by
  let R := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLeftFunctor g
  let p (a : Over S) : R.obj a ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join a.left Y :=
    pullback.fst (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap a.hom g) (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.joinDiagonal S)
  have hu : IsPullback (R.map u) (p A) (p B) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap u.left (𝟙 Y)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLeftMap_isPullback g u.left u.w
  have hv : IsPullback (R.map v) (p A) (p C) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap v.left (𝟙 Y)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLeftMap_isPullback g v.left v.w
  have hr : IsPullback (R.map r) (p B) (p D) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap r.left (𝟙 Y)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLeftMap_isPullback g r.left r.w
  have hs : IsPullback (R.map s) (p C) (p D) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap s.left (𝟙 Y)) :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinLeftMap_isPullback g s.left s.w
  have hw : u ≫ r = v ≫ s := by
    apply Over.OverMorphism.ext
    exact hp.w
  have hc : CommSq (R.map u) (R.map v) (R.map r) (R.map s) := by
    constructor
    rw [← R.map_comp, ← R.map_comp, hw]
  exact ((Adhesive.van_kampen (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.join_left_isPushout hp Y))
    (R.map u) (R.map v) (R.map r) (R.map s) (p A) (p B) (p C) (p D)
    hu hv hr.toCommSq hs.toCommSq hc).mpr ⟨hr, hs⟩

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
