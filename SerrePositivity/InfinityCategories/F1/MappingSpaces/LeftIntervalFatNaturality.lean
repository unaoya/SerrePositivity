module

public import SerrePositivity.InfinityCategories.F1.MappingSpaces.LeftIntervalFatDiagram
public import SerrePositivity.InfinityCategories.Core.FatJoinFunctor

/-!
概要：区間模型の族の fat join 展開の自然性と、coslice fiber 模型上での比較式。
方針：円柱と左右因子への制限で射を比較し、左の点因子の円柱同型を使う。
規約：標的に quasicategory 性は要求しない。
使われ方：Kerodon §4.6.6、coslice fiber 模型の部分族を相対延長で固定する条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：点因子を忘れる円柱の射影はパラメータの射と可換。
方針：各次数で区間成分とパラメータ成分を計算する。
規約：左の標準零単体は恒等射で写す。
使われ方：Kerodon §4.6.6、fat join 展開のパラメータ自然性。 -/
lemma leftIntervalCylinderProjection_naturality {A B : SSet.{u}} (i : A ⟶ B) :
    fatJoinCylinderMap (𝟙 (Δ[0] : SSet.{u})) i ≫ leftIntervalCylinderProjection B =
      leftIntervalCylinderProjection A ≫ (Δ[1] ◁ i) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 概要：区間模型の族の fat join 展開はパラメータの制限と可換。
方針：円柱では射影の自然性、左右では固定端点の式を使う。
規約：パラメータの射 i は任意。
使われ方：Kerodon §4.6.6、部分族上の fat join 図式の計算。 -/
lemma leftIntervalFatDiagram_precomp {A B X : SSet.{u}} {x y : X _⦋0⦌}
    (i : A ⟶ B) (f : B ⟶ intervalMappingSpace x y) :
    fatJoinMap (𝟙 (Δ[0] : SSet.{u})) i ≫ leftIntervalFatDiagram f =
      leftIntervalFatDiagram (i ≫ f) := by
  apply fatJoin_hom_ext
  · rw [← Category.assoc, fatJoinCylinder_map, Category.assoc,
      leftIntervalFatDiagram_cylinder, leftIntervalFatDiagram_cylinder,
      ← Category.assoc, leftIntervalCylinderProjection_naturality,
      Category.assoc, ← intervalMappingUncurry_precomp]
  · rw [← Category.assoc, fatJoinInl_map, Category.id_comp,
      leftIntervalFatDiagram_inl, leftIntervalFatDiagram_inl]
  · rw [← Category.assoc, fatJoinInr_map, Category.assoc,
      leftIntervalFatDiagram_inr, leftIntervalFatDiagram_inr, SSet.comp_const]

/-- 概要：coslice fiber 模型の族の区間展開は通常の join 図式の fat join 比較に一致。
方針：円柱では切断と射影の往復、左右では uncurry の固定端点の式を使う。
規約：元の族 f のパラメータは任意。
使われ方：Kerodon §4.6.6、相対延長の部分族の整合条件。 -/
lemma leftIntervalFatDiagram_comparison {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ vertexFiber (sliceUnderProjection (SSet.yonedaEquiv.symm x)) y) :
    leftIntervalFatDiagram (f ≫ cosliceFiberToIntervalMappingSpace x y) =
      fatJoinComparison Δ[0] A ≫ cosliceFiberUncurry f := by
  have hp : leftIntervalCylinderProjection A ≫ leftMappingSpacePrism A =
      joinCylinderMap Δ[0] A := by
    change leftIntervalCylinderProjection A ≫
      (leftIntervalCylinderSection A ≫ joinCylinderMap Δ[0] A) = _
    rw [← Category.assoc, leftIntervalCylinderProjection_section, Category.id_comp]
  apply fatJoin_hom_ext
  · rw [leftIntervalFatDiagram_cylinder, cosliceFiberToIntervalMappingSpace_uncurry,
      ← Category.assoc, hp, ← Category.assoc, fatJoinCylinder_comparison]
  · rw [leftIntervalFatDiagram_inl, ← Category.assoc,
      fatJoinInl_comparison, cosliceFiberUncurry_inl]
  · rw [leftIntervalFatDiagram_inr, ← Category.assoc,
      fatJoinInr_comparison, cosliceFiberUncurry_inr]

end SerrePositivity.InfinityCategories
