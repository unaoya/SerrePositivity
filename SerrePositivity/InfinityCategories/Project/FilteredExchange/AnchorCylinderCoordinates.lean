module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.IntervalEndpointPullback
public import SerrePositivity.InfinityCategories.Project.FilteredExchange.FiniteAnchorCylinder

/-!
概要：有限写像円柱の元の因子分解先と新しい境界の指定式。
方針：押し出しの二射影と元の円柱の両端を読む。
規約：射影後の円柱は時間に定値。
使われ方：単射な境界への補正が元の境界をホモトピーで固定することの検証。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.FilteredExchange
variable {A L : SSet.{u}} (a : A ⟶ L)

/-- 概要：貼り込んだ元の因子分解先への包含の後の射影は恒等。
方針：押し出しの第二射影。規約：厳密な片逆。使われ方：補正前の射の回収。 -/
lemma anchorCylinder_section_out :
    pushout.inr (SSet.ι₀ : A ⟶ A ⊗ (Δ[1] : SSet.{u})) a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.anchorCylinderOut a = 𝟙 L :=
  pushout.inr_desc _ _ _

/-- 概要：円柱の始点は貼り込んだ元の境界。
方針：押し出しの可換式。規約：始点を貼る。使われ方：補正のホモトピーの始端。 -/
lemma anchorCylinder_prism_zero :
    SSet.ι₀ ≫ pushout.inl (SSet.ι₀ : A ⟶ A ⊗ (Δ[1] : SSet.{u})) a =
      a ≫ pushout.inr (SSet.ι₀ : A ⟶ A ⊗ (Δ[1] : SSet.{u})) a := pushout.condition

/-- 概要：円柱の終点は残した新しい単射な境界。
方針：新しい境界の定義。規約：終点を残す。使われ方：補正後の厳密な境界。 -/
lemma anchorCylinder_prism_one :
    SSet.ι₁ ≫ pushout.inl (SSet.ι₀ : A ⟶ A ⊗ (Δ[1] : SSet.{u})) a = _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.anchorCylinderIn a := rfl

/-- 概要：円柱を元の因子分解先に写すと元の境界射に時間定値。
方針：押し出しの第一射影。規約：全円柱で厳密に一致。使われ方：境界上の相対条件。 -/
lemma anchorCylinder_prism_out :
    pushout.inl (SSet.ι₀ : A ⟶ A ⊗ (Δ[1] : SSet.{u})) a ≫ _root_.SerrePositivity.InfinityCategories.Project.FilteredExchange.anchorCylinderOut a =
      fst A (Δ[1] : SSet.{u}) ≫ a := pushout.inl_desc _ _ _

end SerrePositivity.InfinityCategories.Project.FilteredExchange
