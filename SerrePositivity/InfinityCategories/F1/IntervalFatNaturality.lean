module

public import SerrePositivity.InfinityCategories.F1.IntervalFatDiagram
public import SerrePositivity.InfinityCategories.Core.FatJoinFunctor

/-!
概要：区間模型の族の fat join 展開の自然性と、pinched 模型上での比較式。
方針：円柱と左右因子への制限で射を比較し、点因子の円柱同型を使う。
規約：標的に quasicategory 性は要求しない。
使われ方：Kerodon §4.6.6、pinched 模型の部分族を相対延長で固定する条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：区間の族の fat join 展開を円柱に制限すると元の区間図式を得る。
方針：fat join の貼り合わせの円柱上の式を使う。
規約：円柱の右の点因子は射影で忘れる。
使われ方：Kerodon §4.6.6、fat join 展開の自然性の円柱上の確認。 -/
lemma rightIntervalFatDiagram_cylinder {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ intervalMappingSpace x y) :
    fatJoinCylinder A Δ[0] ≫ rightIntervalFatDiagram f =
      rightIntervalCylinderProjection A ≫ intervalMappingUncurry f :=
  fatJoinCylinder_desc _ _ _ _ _

/-- 概要：点因子を忘れる円柱の射影はパラメータの射と可換。
方針：各次数で区間成分とパラメータ成分を計算する。
規約：右の標準零単体は恒等射で写す。
使われ方：Kerodon §4.6.6、fat join 展開のパラメータ自然性。 -/
lemma rightIntervalCylinderProjection_naturality {A B : SSet.{u}} (i : A ⟶ B) :
    fatJoinCylinderMap i (𝟙 (Δ[0] : SSet.{u})) ≫ rightIntervalCylinderProjection B =
      rightIntervalCylinderProjection A ≫ (Δ[1] ◁ i) := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro a
  rfl

/-- 概要：区間模型の族の fat join 展開はパラメータの制限と可換。
方針：円柱では射影の自然性、左右では固定端点の式を使う。
規約：パラメータの射 i は任意。
使われ方：Kerodon §4.6.6、部分族上の fat join 図式の計算。 -/
lemma rightIntervalFatDiagram_precomp {A B X : SSet.{u}} {x y : X _⦋0⦌}
    (i : A ⟶ B) (f : B ⟶ intervalMappingSpace x y) :
    fatJoinMap i (𝟙 (Δ[0] : SSet.{u})) ≫ rightIntervalFatDiagram f =
      rightIntervalFatDiagram (i ≫ f) := by
  apply fatJoin_hom_ext
  · rw [← Category.assoc, fatJoinCylinder_map, Category.assoc,
      rightIntervalFatDiagram_cylinder, rightIntervalFatDiagram_cylinder,
      ← Category.assoc, rightIntervalCylinderProjection_naturality,
      Category.assoc, ← intervalMappingUncurry_precomp]
  · rw [← Category.assoc, fatJoinInl_map, Category.assoc,
      rightIntervalFatDiagram_inl, rightIntervalFatDiagram_inl, SSet.comp_const]
  · rw [← Category.assoc, fatJoinInr_map, Category.id_comp,
      rightIntervalFatDiagram_inr, rightIntervalFatDiagram_inr]

/-- 概要：pinched 模型の族の区間展開は通常の join 図式の fat join 比較に一致。
方針：円柱では切断と射影の往復、左右では uncurry の固定端点の式を使う。
規約：元の族 f のパラメータは任意。
使われ方：Kerodon §4.6.6、相対延長の部分族の整合条件。 -/
lemma rightIntervalFatDiagram_comparison {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ pinchedHom x y) :
    rightIntervalFatDiagram (f ≫ pinchedHomToIntervalMappingSpace x y) =
      fatJoinComparison A Δ[0] ≫ pinchedHomUncurry f := by
  have hp : rightIntervalCylinderProjection A ≫ rightMappingSpacePrism A =
      joinCylinderMap A Δ[0] := by
    change rightIntervalCylinderProjection A ≫
      (rightIntervalCylinderSection A ≫ joinCylinderMap A Δ[0]) = _
    rw [← Category.assoc, rightIntervalCylinderProjection_section, Category.id_comp]
  apply fatJoin_hom_ext
  · rw [rightIntervalFatDiagram_cylinder, pinchedHomToIntervalMappingSpace_uncurry,
      ← Category.assoc, hp, ← Category.assoc, fatJoinCylinder_comparison]
  · rw [rightIntervalFatDiagram_inl, ← Category.assoc,
      fatJoinInl_comparison, pinchedHomUncurry_inl]
  · rw [rightIntervalFatDiagram_inr, ← Category.assoc,
      fatJoinInr_comparison, pinchedHomUncurry_inr]

end SerrePositivity.InfinityCategories
