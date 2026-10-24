module

public import SerrePositivity.InfinityCategories.F2.FilteredExchange.CoconeUnitCylinder
public import SerrePositivity.InfinityCategories.F1B.Homotopy.HomotopyWhiskering

/-!
概要：図式も頂点も動く余錐の円柱を、その単位の二時間の円柱に移す。
方針：元の join 円柱で前合成し、元の二端の余錐の単位を厳密に回収する。
規約：底の変換を固定と仮定しない。使われ方：余極限関手と native 比較の整合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {K X : SSet.{u}} {f g : K ⟶ X}
  (c : JoinCocone f) (d : JoinCocone g) (H : SSet.Homotopy c.val d.val)

/-- 元の二つの余錐の単位円柱を結ぶ、元の全余錐円柱の制限。 -/
def coconeHomotopyUnitCylinder :
    SSet.Homotopy (coconeTransformationHomotopy c).h
      (coconeTransformationHomotopy d).h where
  h := (coconeUnitCylinderMap K ▷ (Δ[1] : SSet.{u})) ≫ H.h
  h₀ := by
    rw [SSet.ι₀_comp_assoc, H.h₀, coconeTransformationHomotopy_h]
    rfl
  h₁ := by
    rw [SSet.ι₁_comp_assoc, H.h₁, coconeTransformationHomotopy_h]
    rfl
  rel := by
    apply SSet.hom_ext
    intro n
    apply ConcreteCategory.hom_ext
    intro s
    exact False.elim s.1.property

/-- 単位の二時間の円柱の、図式側の時間零の制限。 -/
lemma coconeHomotopyUnitCylinder_source :
    (SSet.ι₀ (X := K) ▷ (Δ[1] : SSet.{u})) ≫
      (coconeHomotopyUnitCylinder c d H).h =
        (joinInl K (Δ[0] : SSet.{u}) ▷ Δ[1]) ≫ H.h := by
  have h : SSet.ι₀ ≫ coconeUnitCylinderMap K = joinInl K (Δ[0] : SSet.{u}) := by
    let e : JoinCocone (joinInl K (Δ[0] : SSet.{u})) := ⟨𝟙 _, Category.comp_id _⟩
    have he := (coconeTransformationHomotopy e).h₀
    simpa only [coconeTransformationHomotopy_h, e, Category.comp_id] using he
  change _ ≫ ((coconeUnitCylinderMap K ▷ Δ[1]) ≫ H.h) = _
  rw [← Category.assoc, ← comp_whiskerRight, h]

/-- 単位の二時間の円柱の、頂点側の時間一の制限。 -/
lemma coconeHomotopyUnitCylinder_target :
    (SSet.ι₁ (X := K) ▷ (Δ[1] : SSet.{u})) ≫
      (coconeHomotopyUnitCylinder c d H).h =
        (SSet.const (SSet.yonedaEquiv (joinInr K (Δ[0] : SSet.{u}))) ▷ Δ[1]) ≫ H.h := by
  have h : SSet.ι₁ ≫ coconeUnitCylinderMap K =
      SSet.const (SSet.yonedaEquiv (joinInr K (Δ[0] : SSet.{u}))) := by
    let e : JoinCocone (joinInl K (Δ[0] : SSet.{u})) := ⟨𝟙 _, Category.comp_id _⟩
    have he := (coconeTransformationHomotopy e).h₁
    simpa only [coconeTransformationHomotopy_h, e, Category.comp_id,
      JoinCocone.vertex_eq] using he
  change _ ≫ ((coconeUnitCylinderMap K ▷ Δ[1]) ≫ H.h) = _
  rw [← Category.assoc, ← comp_whiskerRight, h]

end SerrePositivity.InfinityCategories.F2
