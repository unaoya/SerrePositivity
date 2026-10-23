module

public import SerrePositivity.InfinityCategories.F1.Joins.RelativeJoinCylinder
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingCylinderOverMono

/-!
概要：relative join と写像円柱から係数の底への射影。
方針：relative join は引き戻しの区間付き係数の第二成分、円柱は pushout の両因子の係数を使う。
規約：既存の標準区間への射影とは別に、構造射の終域への射を取る。
使われ方：Kerodon Proposition 5.2.4.5、円柱比較を底上の射として扱う局所判定。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：relative join の共通の係数の底への射影。
方針：引き戻しの第二射影の区間成分を忘れる。
規約：任意の共通の底への二つの射を許す。
使われ方：Kerodon Construction 5.2.3.1、Proposition 5.2.4.5 の底変換。 -/
noncomputable def relativeJoinBaseProjection {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    relativeJoin f g ⟶ S :=
  pullback.snd (joinMap f g) (joinDiagonal S) ≫ snd (Δ[1] : SSet.{u}) S

/-- 概要：relative join の右包含は係数の底への射影と可換。
方針：持ち上げの第二射影と prism の終点の係数射影を計算する。
規約：右因子の構造射は g。
使われ方：Kerodon Proposition 5.2.4.5、円柱の終域部分での底上の可換性。 -/
lemma relativeJoinInr_baseProjection {X Y S : SSet.{u}} (f : X ⟶ S) (g : Y ⟶ S) :
    relativeJoinInr f g ≫ relativeJoinBaseProjection f g = g := by
  rw [relativeJoinBaseProjection, ← Category.assoc, relativeJoinInr, pullback.lift_snd,
    Category.assoc, prismEndpoint_snd, Category.comp_id]

/-- 概要：relative join への prism は係数の射 f と可換。
方針：pullback の第二射影を計算し、区間との直積の係数射影を使う。
規約：prism の係数側は X、relative join の底は Y。
使われ方：Kerodon Proposition 5.2.4.5、円柱部分での底上の可換性。 -/
lemma relativeJoinPrism_baseProjection {X Y : SSet.{u}} (f : X ⟶ Y) :
    relativeJoinPrism f ≫ relativeJoinBaseProjection f (𝟙 Y) =
      snd (Δ[1] : SSet.{u}) X ≫ f := by
  rw [relativeJoinBaseProjection, ← Category.assoc, relativeJoinPrism, pullback.lift_snd]
  exact whiskerLeft_snd (Δ[1] : SSet.{u}) f

/-- 概要：写像円柱の係数の底への射影。
方針：円柱部分の係数に f を合成し、終域部分では恒等射を使って貼る。
規約：prism の一端を f に沿って貼る写像円柱。
使われ方：Kerodon Proposition 5.2.4.5、底の各単体へ比較を引き戻す射。 -/
noncomputable def mappingCylinderBaseProjection {X Y : SSet.{u}} (f : X ⟶ Y) :
    pushout (prismEndpoint 1 X) f ⟶ Y :=
  pushout.desc (snd (Δ[1] : SSet.{u}) X ≫ f) (𝟙 Y) (by
    rw [← Category.assoc, prismEndpoint_snd, Category.id_comp, Category.comp_id])

/-- 概要：円柱の係数射影は円柱部分で係数の射 f と一致する。
方針：pushout の左包含の計算則を使う。
規約：区間の位置によらず係数を写す。
使われ方：Kerodon Proposition 5.2.4.5、底変換の円柱部分の計算。 -/
lemma mappingCylinderBaseProjection_inl {X Y : SSet.{u}} (f : X ⟶ Y) :
    pushout.inl (prismEndpoint 1 X) f ≫ mappingCylinderBaseProjection f =
      snd (Δ[1] : SSet.{u}) X ≫ f := pushout.inl_desc _ _ _

/-- 概要：円柱の係数射影は終域部分で恒等射。
方針：pushout の右包含の計算則を使う。
規約：終域の係数を厳密に保つ。
使われ方：Kerodon Proposition 5.2.4.5、底変換の終域部分の計算。 -/
lemma mappingCylinderBaseProjection_inr {X Y : SSet.{u}} (f : X ⟶ Y) :
    pushout.inr (prismEndpoint 1 X) f ≫ mappingCylinderBaseProjection f = 𝟙 Y :=
  pushout.inr_desc _ _ _

/-- 概要：写像円柱比較は係数の底への射影を保つ。
方針：pushout の二つの因子で prism と右包含の係数射影を計算する。
規約：底は構造射 f の終域 Y。
使われ方：Kerodon Proposition 5.2.4.5、比較の底上の射としての表示。 -/
lemma relativeJoinCylinderComparison_baseProjection {X Y : SSet.{u}} (f : X ⟶ Y) :
    relativeJoinCylinderComparison f ≫ relativeJoinBaseProjection f (𝟙 Y) =
      mappingCylinderBaseProjection f := by
  apply pushout.hom_ext
  · rw [← Category.assoc, relativeJoinCylinderComparison_inl,
      relativeJoinPrism_baseProjection, mappingCylinderBaseProjection_inl]
  · rw [← Category.assoc, relativeJoinCylinderComparison_inr,
      relativeJoinInr_baseProjection, mappingCylinderBaseProjection_inr]

/-- 概要：係数の底上の射としての写像円柱比較。
方針：既存の比較射と係数射影との可換性を束ねる。
規約：左成分は既存の relativeJoinCylinderComparison。
使われ方：Kerodon Proposition 5.2.4.5、各標準単体への pullback による局所判定。 -/
noncomputable def relativeJoinCylinderComparisonOver {X Y : SSet.{u}} (f : X ⟶ Y) :
    Over.mk (mappingCylinderBaseProjection f) ⟶ Over.mk (relativeJoinBaseProjection f (𝟙 Y)) :=
  Over.homMk (relativeJoinCylinderComparison f) (relativeJoinCylinderComparison_baseProjection f)

end SerrePositivity.InfinityCategories
