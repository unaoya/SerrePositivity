module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.OverPullbackColimits

/-!
概要：底上の射の pullback を底の対象に自然な比較にまとめる。
方針：第一成分を保ち、固定した対象の第二成分を底上の射で写す。
規約：底 S は固定する。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、各標準単体への制限の比較。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：底上の射を任意の底上の対象に沿って pullback した射。
方針：第一射影と底上の射を合成した第二射影を pullback へ持ち上げる。
規約：第一成分は可変の底上の対象 z。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、単体ごとの比較射。 -/
noncomputable def overPullbackMap {S : SSet.{u}} {a b : Over S} (u : a ⟶ b) (z : Over S) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying a.hom).obj z ⟶ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying b.hom).obj z :=
  pullback.lift (pullback.fst z.hom a.hom) (pullback.snd z.hom a.hom ≫ u.left) (by
    rw [Category.assoc, u.w]
    exact pullback.condition)

/-- 概要：pullback した射は可変の底の対象への第一射影を保つ。
方針：pullback の持ち上げの第一射影の計算則を使う。
規約：底上の射と底の対象は任意。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、pullback の比較の自然性。 -/
lemma overPullbackMap_fst {S : SSet.{u}} {a b : Over S} (u : a ⟶ b) (z : Over S) :
    overPullbackMap u z ≫ pullback.fst z.hom b.hom = pullback.fst z.hom a.hom :=
  pullback.lift_fst _ _ _

/-- 概要：pullback した射の第二射影は元の底上の射との合成。
方針：pullback の持ち上げの第二射影の計算則を使う。
規約：元の射 u の左成分を使う。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、恒等な底で元の比較射を回収する。 -/
lemma overPullbackMap_snd {S : SSet.{u}} {a b : Over S} (u : a ⟶ b) (z : Over S) :
    overPullbackMap u z ≫ pullback.snd z.hom b.hom = pullback.snd z.hom a.hom ≫ u.left :=
  pullback.lift_snd _ _ _

/-- 概要：底上の射の pullback は可変の底上の対象に自然。
方針：pullback の両射影で二種類の誘導射の計算則を照合する。
規約：u が固定した比較、v が底の対象の変更。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、セル分解に沿う自然な比較。 -/
lemma overPullbackMap_naturality {S : SSet.{u}} {a b z w : Over S}
    (u : a ⟶ b) (v : z ⟶ w) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying a.hom).map v ≫ overPullbackMap u w =
      overPullbackMap u z ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying b.hom).map v := by
  apply pullback.hom_ext
  · rw [Category.assoc, overPullbackMap_fst, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying_map_fst,
      Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying_map_fst, ← Category.assoc, overPullbackMap_fst]
  · rw [Category.assoc, overPullbackMap_snd, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying_map_snd, Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying_map_snd,
      overPullbackMap_snd]

/-- 概要：底上の射の全ての pullback を自然変換にまとめる。
方針：pullback した射を各成分とし、両射影による自然性を使う。
規約：始域・終域の関手は同じ底に向かう Over 圏上の関手。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、底の各標準単体での比較判定。 -/
noncomputable def overPullbackMapNat {S : SSet.{u}} {a b : Over S} (u : a ⟶ b) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying a.hom ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.overPullbackUnderlying b.hom where
  app z := overPullbackMap u z
  naturality _ _ v := overPullbackMap_naturality u v

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
