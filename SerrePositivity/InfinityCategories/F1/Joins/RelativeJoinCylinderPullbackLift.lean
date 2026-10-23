module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingCylinderPullbackMap
public import SerrePositivity.InfinityCategories.F1.Diagrams.OverPullbackMorphism

/-!
概要：底変換した円柱と relative join から係数の底への pullback への標準射。
方針：係数射影と元の模型への射を pullback に持ち上げ、比較との可換性を両射影で示す。
規約：ここでは射と計算則を構成し、同型性は別に検証する。
使われ方：Kerodon Proposition 5.2.4.5、局所判定の pullback と具体的な円柱比較の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
namespace SerrePositivity.InfinityCategories

/-- 概要：底変換した写像円柱から係数射影の pullback への標準射。
方針：新しい係数射影と元の円柱への射を組にする。
規約：第一射影の終域は Z、第二射影の終域は元の写像円柱。
使われ方：Kerodon Proposition 5.2.4.5、写像円柱の底変換との同定。 -/
noncomputable def mappingCylinderPullbackLift {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    pushout (prismEndpoint 1 (pullback f h)) (pullback.snd f h) ⟶
      pullback h (mappingCylinderBaseProjection f) :=
  pullback.lift (mappingCylinderBaseProjection (pullback.snd f h))
    (mappingCylinderPullbackMap f h) (mappingCylinderPullbackMap_baseProjection f h).symm

/-- 概要：円柱からの持ち上げの第一射影は新しい係数射影。
方針：pullback の持ち上げの第一射影を計算する。
規約：底変換の底は Z。
使われ方：Kerodon Proposition 5.2.4.5、具体的な円柱の底への射。 -/
lemma mappingCylinderPullbackLift_fst {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    mappingCylinderPullbackLift f h ≫ pullback.fst h (mappingCylinderBaseProjection f) =
      mappingCylinderBaseProjection (pullback.snd f h) := pullback.lift_fst _ _ _

/-- 概要：円柱からの持ち上げの第二射影は元の円柱への標準射。
方針：pullback の持ち上げの第二射影を計算する。
規約：係数の射 h に沿う元の模型への射。
使われ方：Kerodon Proposition 5.2.4.5、元の円柱比較との可換性。 -/
lemma mappingCylinderPullbackLift_snd {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    mappingCylinderPullbackLift f h ≫ pullback.snd h (mappingCylinderBaseProjection f) =
      mappingCylinderPullbackMap f h := pullback.lift_snd _ _ _

/-- 概要：底変換した relative join から係数射影の pullback への標準射。
方針：新しい係数射影と元の relative join への射を組にする。
規約：第一射影の終域は Z、第二射影の終域は元の relative join。
使われ方：Kerodon Proposition 5.2.4.5、relative join の底変換との同定。 -/
noncomputable def relativeJoinPullbackLift {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    relativeJoin (pullback.snd f h) (𝟙 Z) ⟶ pullback h (relativeJoinBaseProjection f (𝟙 Y)) :=
  pullback.lift (relativeJoinBaseProjection (pullback.snd f h) (𝟙 Z))
    (relativeJoinPullbackMap f h) (relativeJoinPullbackMap_baseProjection f h).symm

/-- 概要：relative join からの持ち上げの第一射影は新しい係数射影。
方針：pullback の持ち上げの第一射影を計算する。
規約：底変換の底は Z。
使われ方：Kerodon Proposition 5.2.4.5、具体的な relative join の底への射。 -/
lemma relativeJoinPullbackLift_fst {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    relativeJoinPullbackLift f h ≫ pullback.fst h (relativeJoinBaseProjection f (𝟙 Y)) =
      relativeJoinBaseProjection (pullback.snd f h) (𝟙 Z) := pullback.lift_fst _ _ _

/-- 概要：relative join からの持ち上げの第二射影は元の模型への標準射。
方針：pullback の持ち上げの第二射影を計算する。
規約：係数の射 h に沿う元の模型への射。
使われ方：Kerodon Proposition 5.2.4.5、元の円柱比較との可換性。 -/
lemma relativeJoinPullbackLift_snd {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    relativeJoinPullbackLift f h ≫ pullback.snd h (relativeJoinBaseProjection f (𝟙 Y)) =
      relativeJoinPullbackMap f h := pullback.lift_snd _ _ _

/-- 概要：具体的な底変換後の円柱比較と底上の射の pullback は標準の持ち上げで可換。
方針：二つの pullback 射影で係数射影の可換性と元の比較の自然性を使う。
規約：比較の持ち上げの同型性は仮定しない。
使われ方：Kerodon Proposition 5.2.4.5、標準単体上の比較を局所判定へ渡す正方形。 -/
lemma relativeJoinCylinderComparison_pullbackLift {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    relativeJoinCylinderComparison (pullback.snd f h) ≫ relativeJoinPullbackLift f h =
      mappingCylinderPullbackLift f h ≫
        overPullbackMap (relativeJoinCylinderComparisonOver f) (Over.mk h) := by
  have hfst := overPullbackMap_fst (relativeJoinCylinderComparisonOver f) (Over.mk h)
  change overPullbackMap (relativeJoinCylinderComparisonOver f) (Over.mk h) ≫
    pullback.fst h (relativeJoinBaseProjection f (𝟙 Y)) =
      pullback.fst h (mappingCylinderBaseProjection f) at hfst
  have hsnd := overPullbackMap_snd (relativeJoinCylinderComparisonOver f) (Over.mk h)
  change overPullbackMap (relativeJoinCylinderComparisonOver f) (Over.mk h) ≫
    pullback.snd h (relativeJoinBaseProjection f (𝟙 Y)) =
      pullback.snd h (mappingCylinderBaseProjection f) ≫ relativeJoinCylinderComparison f at hsnd
  apply pullback.hom_ext
  · rw [Category.assoc, relativeJoinPullbackLift_fst,
      relativeJoinCylinderComparison_baseProjection, Category.assoc, hfst,
      mappingCylinderPullbackLift_fst]
  · rw [Category.assoc, relativeJoinPullbackLift_snd,
      ← relativeJoinCylinderComparison_pullbackMap, Category.assoc, hsnd,
      ← Category.assoc, mappingCylinderPullbackLift_snd]

end SerrePositivity.InfinityCategories
