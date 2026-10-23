module
public import SerrePositivity.KST.Fibration.PointSourceFatDiagram
public import SerrePositivity.InfinityCategories.F1.MappingSpaces.LeftIntervalFatHomotopy

/-! # 始点固定の同じ可変終点矢印族を部分族へ制限する厳密な円柱式 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration

/-- 左の点を補う切断は、元のパラメータの射と厳密に可換。 -/
theorem leftIntervalCylinderSection_naturality {P A : SSet.{u}} (i : P ⟶ A) :
    leftIntervalCylinderSection P ≫ fatJoinCylinderMap (𝟙 (Δ[0] : SSet.{u})) i =
      (Δ[1] ◁ i) ≫ leftIntervalCylinderSection A := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  rfl

/-- 同じ fat prism の部分族への制限は、元の prism のパラメータの制限そのもの。 -/
theorem leftIntervalFatPrism_naturality {P A : SSet.{u}} (i : P ⟶ A) :
    leftIntervalFatPrism P ≫ fatJoinMap (𝟙 (Δ[0] : SSet.{u})) i =
      (Δ[1] ◁ i) ≫ leftIntervalFatPrism A := by
  rw [leftIntervalFatPrism, leftIntervalFatPrism, Category.assoc, fatJoinCylinder_map,
    ← Category.assoc, leftIntervalCylinderSection_naturality, Category.assoc]

/-- 元の fat join 表示を同じ部分族へ制限すると、元の矢印族の制限を回収する。 -/
theorem pointSourceFatDiagram_restrict_recover {A P X : SSet.{u}}
    (x : X _⦋0⦌) (g : A ⟶ X) (f : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
    (h₀ : prismEndpoint 0 A ≫ uncurry f = SSet.const x)
    (h₁ : prismEndpoint 1 A ≫ uncurry f = g) (i : P ⟶ A) :
    leftIntervalFatPrism P ≫ (fatJoinMap (𝟙 (Δ[0] : SSet.{u})) i ≫
      pointSourceFatDiagram x g f h₀ h₁) = uncurry (i ≫ f) := by
  rw [← Category.assoc, leftIntervalFatPrism_naturality, Category.assoc]
  change (Δ[1] ◁ i) ≫ (leftIntervalCylinderSection A ≫ fatJoinCylinder Δ[0] A ≫
    pointSourceFatDiagram x g f h₀ h₁) = _
  rw [pointSourceFatDiagram_recover, uncurry_natural_left]

end SerrePositivity.KST.Fibration
