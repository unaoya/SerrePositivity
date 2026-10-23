module

public import SerrePositivity.InfinityCategories.F1.Joins.RelativeJoinCylinder
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.MappingCylinderOverMono
public import Mathlib.CategoryTheory.Adhesive.Basic

/-!
概要：単射の写像円柱から relative join への比較の単射性。
方針：係数付き区間への射を pushout と pullback の単射判定で調べる。
規約：構造射 f の単射性だけを要求し、充填性は要求しない。
使われ方：Kerodon Theorem 5.2.4.1、円柱上の射を relative join 全体へ延長する段階。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：写像円柱から終域を係数とする区間への射。
方針：円柱部分は f で係数を写し、終域部分は区間の終点に置く。
規約：区間成分と係数成分の両方を保持する。
使われ方：Kerodon Theorem 5.2.4.1、円柱比較の単射性を判定する補助射。 -/
noncomputable def mappingCylinderPrismMap {X Y : SSet.{u}} (f : X ⟶ Y) :
    pushout (prismEndpoint 1 X) f ⟶ (Δ[1] : SSet.{u}) ⊗ Y :=
  pushout.desc ((Δ[1] : SSet.{u}) ◁ f) (prismEndpoint 1 Y) (prismEndpoint_naturality 1 f)

/-- 概要：単射の写像円柱から係数付き区間への射は単射。
方針：prism の端点の自然性の pullback に adhesive な圏の単射判定を使う。
規約：構造射 f は単射。
使われ方：Kerodon Theorem 5.2.4.1、relative join への比較の単射性。 -/
instance mappingCylinderPrismMap_mono {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    Mono (mappingCylinderPrismMap f) := by
  have : Mono ((Δ[1] : SSet.{u}) ◁ f) := (tensorLeft _).map_mono f
  let hp := IsPushout.of_hasPushout (prismEndpoint 1 X) f
  let hq := isPullback_prismEndpoint_naturality 1 f
  have he : hp.desc ((Δ[1] : SSet.{u}) ◁ f) (prismEndpoint 1 Y) hq.w =
      mappingCylinderPrismMap f := by
    apply pushout.hom_ext
    · rw [hp.inl_desc, mappingCylinderPrismMap, pushout.inl_desc]
    · rw [hp.inr_desc, mappingCylinderPrismMap, pushout.inr_desc]
  rw [← he]
  exact hp.desc_mono_of_isPullback hq

/-- 概要：円柱比較を係数付き区間へ写すと円柱の標準射になる。
方針：円柱部分と終域部分で pullback の第二射影を計算する。
規約：relative join の構造射は f と終域の恒等射。
使われ方：Kerodon Theorem 5.2.4.1、比較の単射性を係数付き区間で検査する。 -/
lemma relativeJoinCylinderComparison_prismMap {X Y : SSet.{u}} (f : X ⟶ Y) :
    relativeJoinCylinderComparison f ≫ pullback.snd (joinMap f (𝟙 Y)) (joinDiagonal Y) =
      mappingCylinderPrismMap f := by
  apply pushout.hom_ext
  · rw [← Category.assoc, relativeJoinCylinderComparison_inl, relativeJoinPrism,
      pullback.lift_snd, mappingCylinderPrismMap, pushout.inl_desc]
  · rw [← Category.assoc, relativeJoinCylinderComparison_inr, relativeJoinInr,
      pullback.lift_snd, Category.id_comp, mappingCylinderPrismMap, pushout.inr_desc]

/-- 概要：単射の写像円柱から relative join への標準比較は単射。
方針：係数付き区間への合成が単射であることから前の射の単射性を得る。
規約：始域と終域の quasicategory 性は要求しない。
使われ方：Kerodon Theorem 5.2.4.1、比較に沿う射の厳密な延長。 -/
instance relativeJoinCylinderComparison_mono {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] :
    Mono (relativeJoinCylinderComparison f) :=
  mono_of_mono_fac (relativeJoinCylinderComparison_prismMap f)

end SerrePositivity.InfinityCategories
