module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.LeftIntervalFatNaturality

/-! # 始点を固定し終点を動かす元の矢印族の fat join 展開 -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
open SerrePositivity.InfinityCategories
namespace SerrePositivity.KST.Fibration
variable {A X : SSet.{u}} (x : X _⦋0⦌) (g : A ⟶ X)
  (f : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
  (h₀ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A ≫ uncurry f = SSet.const x)
  (h₁ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 A ≫ uncurry f = g)

/-- 元の始点と可変の終点図式を、同じ矢印族の円柱に貼り合わせる。 -/
def pointSourceFatDiagram : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoin (Δ[0] : SSet.{u}) A ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinDesc (yonedaEquiv.symm x) g (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftIntervalCylinderProjection A ≫ uncurry f) (by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftIntervalCylinderProjection_zero, Category.assoc, h₀,
      SSet.comp_const]
    have he : fst (Δ[0] : SSet.{u}) A = SSet.const (stdSimplex.obj₀Equiv.symm 0) :=
      stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [he, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.const_point_comp_yoneda]) (by
    rw [← Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftIntervalCylinderProjection_one, Category.assoc, h₁])

/-- 左の点は元の固定始点そのもの。 -/
theorem pointSourceFatDiagram_inl :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl Δ[0] A ≫ pointSourceFatDiagram x g f h₀ h₁ = yonedaEquiv.symm x :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInl_desc _ _ _ _ _

/-- 右因子は元の可変終点図式そのもの。 -/
theorem pointSourceFatDiagram_inr :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr Δ[0] A ≫ pointSourceFatDiagram x g f h₀ h₁ = g :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinInr_desc _ _ _ _ _

/-- 元の同じ全パラメータ矢印族を円柱から厳密に回収する。 -/
theorem pointSourceFatDiagram_recover :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftIntervalCylinderSection A ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder Δ[0] A ≫
      pointSourceFatDiagram x g f h₀ h₁ = uncurry f := by
  rw [pointSourceFatDiagram, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fatJoinCylinder_desc, ← Category.assoc,
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.leftIntervalCylinderSection_projection, Category.id_comp]

end SerrePositivity.KST.Fibration
