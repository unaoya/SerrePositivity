module

public import SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.RelativeJoinPullbackMap

/-!
概要：構造射の pullback が誘導する写像円柱の比較と relative join への自然性。
方針：区間付き第一射影と底の射を pushout で貼り、円柱比較の両因子で検査する。
規約：底変換の射 h に制限を課さない。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、各標準単体への pullback と円柱比較の接続。

対応節は Kerodon 5.2（Tag 019A）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport

/-- 概要：底変換した構造射の写像円柱から元の写像円柱への標準射。
方針：円柱部分に区間付き第一射影、終域部分に h を使って pushout から貼る。
規約：底変換した構造射は pullback の第二射影。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、円柱の底変換の同定。 -/
noncomputable def mappingCylinderPullbackMap {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (pullback f h)) (pullback.snd f h) ⟶
      pushout (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 X) f :=
  pushout.desc
    (((Δ[1] : SSet.{u}) ◁ pullback.fst f h) ≫ pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 X) f)
    (h ≫ pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 X) f) (by
      rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint_naturality, Category.assoc, pushout.condition,
        ← Category.assoc, pullback.condition, Category.assoc])

/-- 概要：円柱の底変換の比較は円柱部分で区間付き第一射影と一致する。
方針：pushout の左包含の計算則を使う。
規約：区間は恒等で保つ。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、円柱部分の底変換の計算。 -/
lemma mappingCylinderPullbackMap_inl {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (pullback f h)) (pullback.snd f h) ≫
      mappingCylinderPullbackMap f h =
        ((Δ[1] : SSet.{u}) ◁ pullback.fst f h) ≫ pushout.inl (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 X) f :=
  pushout.inl_desc _ _ _

/-- 概要：円柱の底変換の比較は終域部分で h と一致する。
方針：pushout の右包含の計算則を使う。
規約：終域部分の係数を h で写す。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、終域部分の底変換の計算。 -/
lemma mappingCylinderPullbackMap_inr {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 (pullback f h)) (pullback.snd f h) ≫
      mappingCylinderPullbackMap f h = h ≫ pushout.inr (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 X) f :=
  pushout.inr_desc _ _ _

/-- 概要：円柱の底変換の比較は係数の底への射影と可換。
方針：円柱部分で構造射の pullback の可換性、終域部分で恒等射の式を使う。
規約：底の射は h。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、底への pullback に持ち上げる条件。 -/
lemma mappingCylinderPullbackMap_baseProjection {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    mappingCylinderPullbackMap f h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection (pullback.snd f h) ≫ h := by
  apply pushout.hom_ext
  · rw [← Category.assoc, mappingCylinderPullbackMap_inl, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection_inl, ← Category.assoc, whiskerLeft_snd,
      Category.assoc, pullback.condition, ← Category.assoc,
      ← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection_inl]
  · rw [← Category.assoc, mappingCylinderPullbackMap_inr, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection_inr, Category.comp_id, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.mappingCylinderBaseProjection_inr, Category.id_comp]

/-- 概要：写像円柱から relative join への比較は構造射の底変換と可換。
方針：pushout の二つの因子で prism と右包含の底変換の式を使う。
規約：両側とも既存の標準比較射を使う。
使われ方：Kerodon Proposition 5.2.4.5（Tag 024R）、標準単体上の比較を局所判定へ移す正方形。 -/
lemma relativeJoinCylinderComparison_pullbackMap {X Y Z : SSet.{u}} (f : X ⟶ Y) (h : Z ⟶ Y) :
    mappingCylinderPullbackMap f h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison f =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison (pullback.snd f h) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPullbackMap f h := by
  apply pushout.hom_ext
  · rw [← Category.assoc, mappingCylinderPullbackMap_inl, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison_inl, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison_inl, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinPrism_pullbackMap]
  · rw [← Category.assoc, mappingCylinderPullbackMap_inr, Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison_inr, ← Category.assoc,
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinCylinderComparison_inr, _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport.relativeJoinInr_pullbackMap]

end SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CovariantTransport
