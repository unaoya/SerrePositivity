module

public import SerrePositivity.InfinityCategories.F1.Joins.RelativeJoinBaseProjection

/-!
概要：構造射の pullback が誘導する relative join の比較射。
方針：通常の join と区間付き係数の両成分を写して pullback に持ち上げる。
規約：始域の構造射は pullback の第二射影。
使われ方：Kerodon Proposition 5.2.4.5、底変換した比較と元の比較の接続。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：底変換した構造射の relative join から元の relative join への標準射。
方針：左因子に pullback の第一射影、右因子と係数に底変換の射 h を適用する。
規約：ここでは射と計算則を構成し、正方形の pullback 性は別に検証する。
使われ方：Kerodon Proposition 5.2.4.5、底変換後の relative join の同定。 -/
noncomputable def relativeJoinPullbackMap {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    relativeJoin (pullback.snd f h) (𝟙 Z) ⟶ relativeJoin f (𝟙 Y) :=
  pullback.lift
    (pullback.fst (joinMap (pullback.snd f h) (𝟙 Z)) (joinDiagonal Z) ≫
      joinMap (pullback.fst f h) h)
    (pullback.snd (joinMap (pullback.snd f h) (𝟙 Z)) (joinDiagonal Z) ≫ ((Δ[1] : SSet.{u}) ◁ h))
    (by
      have hj : joinMap (pullback.fst f h) h ≫ joinMap f (𝟙 Y) =
          joinMap (pullback.snd f h) (𝟙 Z) ≫ joinMap h h := by
        rw [← joinMap_comp, ← joinMap_comp, pullback.condition,
          Category.comp_id, Category.id_comp]
      rw [Category.assoc, hj, ← Category.assoc, pullback.condition, Category.assoc,
        Category.assoc, joinDiagonal_naturality])

/-- 概要：底変換の比較の第一射影は二つの因子の射の join。
方針：pullback の持ち上げの第一射影を計算する。
規約：左因子は第一射影、右因子は h。
使われ方：Kerodon Proposition 5.2.4.5、次数ごとの pullback の成分。 -/
lemma relativeJoinPullbackMap_fst {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    relativeJoinPullbackMap f h ≫ pullback.fst (joinMap f (𝟙 Y)) (joinDiagonal Y) =
      pullback.fst (joinMap (pullback.snd f h) (𝟙 Z)) (joinDiagonal Z) ≫
        joinMap (pullback.fst f h) h := pullback.lift_fst _ _ _

/-- 概要：底変換の比較の第二射影は区間を保ち係数に h を合成する。
方針：pullback の持ち上げの第二射影を計算する。
規約：係数の底は Z から Y へ写る。
使われ方：Kerodon Proposition 5.2.4.5、底上の可換性。 -/
lemma relativeJoinPullbackMap_snd {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    relativeJoinPullbackMap f h ≫ pullback.snd (joinMap f (𝟙 Y)) (joinDiagonal Y) =
      pullback.snd (joinMap (pullback.snd f h) (𝟙 Z)) (joinDiagonal Z) ≫
        ((Δ[1] : SSet.{u}) ◁ h) := pullback.lift_snd _ _ _

/-- 概要：relative join の底変換の比較は係数の底への射影と可換。
方針：第二射影と区間との直積の係数射影を計算する。
規約：底の射は h。
使われ方：Kerodon Proposition 5.2.4.5、底の各単体への pullback の正方形。 -/
lemma relativeJoinPullbackMap_baseProjection {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    relativeJoinPullbackMap f h ≫ relativeJoinBaseProjection f (𝟙 Y) =
      relativeJoinBaseProjection (pullback.snd f h) (𝟙 Z) ≫ h := by
  rw [relativeJoinBaseProjection, ← Category.assoc, relativeJoinPullbackMap_snd,
    Category.assoc, whiskerLeft_snd, ← Category.assoc]
  rfl

/-- 概要：relative join の底変換は prism の係数の第一射影と可換。
方針：pullback の両射影で対角の自然性と構造射の pullback の可換性を使う。
規約：区間成分は恒等射。
使われ方：Kerodon Proposition 5.2.4.5、円柱部分での比較の底変換。 -/
lemma relativeJoinPrism_pullbackMap {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    relativeJoinPrism (pullback.snd f h) ≫ relativeJoinPullbackMap f h =
      ((Δ[1] : SSet.{u}) ◁ pullback.fst f h) ≫ relativeJoinPrism f := by
  unfold relativeJoinPrism
  apply pullback.hom_ext
  · rw [Category.assoc, relativeJoinPullbackMap_fst, ← Category.assoc,
      pullback.lift_fst, Category.assoc, ← joinMap_comp, Category.id_comp,
      Category.assoc, pullback.lift_fst, ← Category.assoc, joinDiagonal_naturality,
      Category.assoc, ← joinMap_comp, Category.comp_id, pullback.condition]
  · rw [Category.assoc, relativeJoinPullbackMap_snd, ← Category.assoc,
      pullback.lift_snd, Category.assoc, pullback.lift_snd,
      ← whiskerLeft_comp, ← whiskerLeft_comp, pullback.condition]

/-- 概要：relative join の底変換は右因子の包含と可換。
方針：第一射影で join の右包含、第二射影で prism の終点の自然性を使う。
規約：右因子の射は h。
使われ方：Kerodon Proposition 5.2.4.5、円柱の終域部分での比較の底変換。 -/
lemma relativeJoinInr_pullbackMap {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    relativeJoinInr (pullback.snd f h) (𝟙 Z) ≫ relativeJoinPullbackMap f h =
      h ≫ relativeJoinInr f (𝟙 Y) := by
  apply pullback.hom_ext
  · rw [Category.assoc, relativeJoinPullbackMap_fst, ← Category.assoc,
      relativeJoinInr_fst, joinInr_joinMap, Category.assoc, relativeJoinInr_fst]
  · rw [Category.assoc, relativeJoinPullbackMap_snd, ← Category.assoc,
      relativeJoinInr, pullback.lift_snd, Category.id_comp]
    rw [Category.assoc, relativeJoinInr, pullback.lift_snd, Category.id_comp]
    exact prismEndpoint_naturality 1 h

end SerrePositivity.InfinityCategories
