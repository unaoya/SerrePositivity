module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.ConeCylinderMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.FatJoinComparisonNaturality

/-!
概要：native な錐の円柱への写像は、右の形状の制限に厳密に自然。
方針：左の一点の補充と、既存の join 円柱の自然性を合成する。
規約：形状写像は任意であり、元の円柱を置き換えない。
使われ方：錐から定値始域の変換への全族比較の自然性。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions

/-- 円柱へ左の一点を補う操作は、右の形状写像と可換。 -/
lemma fatConeCylinderEmbedding_naturality {A K : SSet.{u}} (i : A ⟶ K) :
    (i ▷ (Δ[1] : SSet.{u})) ≫ fatConeCylinderEmbedding K =
      fatConeCylinderEmbedding A ≫ fatJoinCylinderMap (𝟙 (Δ[0] : SSet.{u})) i := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro x
  rfl

/-- 元の錐の円柱は、形状の制限後も同じ join への写像になる。 -/
lemma coneCylinderMap_naturality {A K : SSet.{u}} (i : A ⟶ K) :
    (i ▷ (Δ[1] : SSet.{u})) ≫ coneCylinderMap K =
      coneCylinderMap A ≫ joinMap (𝟙 (Δ[0] : SSet.{u})) i := by
  simp only [coneCylinderMap, fatJoinCylinder_comparison]
  rw [← Category.assoc, fatConeCylinderEmbedding_naturality, Category.assoc,
    joinCylinderMap_naturality, ← Category.assoc]

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions
