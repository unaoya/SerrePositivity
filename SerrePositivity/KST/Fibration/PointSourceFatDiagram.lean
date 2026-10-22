module
public import SerrePositivity.InfinityCategories.F1.LeftIntervalFatNaturality

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
  (h₀ : prismEndpoint 0 A ≫ uncurry f = SSet.const x)
  (h₁ : prismEndpoint 1 A ≫ uncurry f = g)

/-- 元の始点と可変の終点図式を、同じ矢印族の円柱に貼り合わせる。 -/
def pointSourceFatDiagram : fatJoin (Δ[0] : SSet.{u}) A ⟶ X :=
  fatJoinDesc (yonedaEquiv.symm x) g (leftIntervalCylinderProjection A ≫ uncurry f) (by
    rw [← Category.assoc, leftIntervalCylinderProjection_zero, Category.assoc, h₀,
      SSet.comp_const]
    have he : fst (Δ[0] : SSet.{u}) A = SSet.const (stdSimplex.obj₀Equiv.symm 0) :=
      stdSimplex.isTerminalObj₀.hom_ext _ _
    rw [he, const_point_comp_yoneda]) (by
    rw [← Category.assoc, leftIntervalCylinderProjection_one, Category.assoc, h₁])

/-- 左の点は元の固定始点そのもの。 -/
theorem pointSourceFatDiagram_inl :
    fatJoinInl Δ[0] A ≫ pointSourceFatDiagram x g f h₀ h₁ = yonedaEquiv.symm x :=
  fatJoinInl_desc _ _ _ _ _

/-- 右因子は元の可変終点図式そのもの。 -/
theorem pointSourceFatDiagram_inr :
    fatJoinInr Δ[0] A ≫ pointSourceFatDiagram x g f h₀ h₁ = g :=
  fatJoinInr_desc _ _ _ _ _

/-- 元の同じ全パラメータ矢印族を円柱から厳密に回収する。 -/
theorem pointSourceFatDiagram_recover :
    leftIntervalCylinderSection A ≫ fatJoinCylinder Δ[0] A ≫
      pointSourceFatDiagram x g f h₀ h₁ = uncurry f := by
  rw [pointSourceFatDiagram, fatJoinCylinder_desc, ← Category.assoc,
    leftIntervalCylinderSection_projection, Category.id_comp]

end SerrePositivity.KST.Fibration
