module

public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.Cocone
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.Join
public import SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.CoconeTransformationVertex
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.CoconeUnitCylinder

/-!
概要：図式も頂点も動く余錐の円柱を、その単位の二時間の円柱に移す。
方針：元の join 円柱で前合成し、元の二端の余錐の単位を厳密に回収する。
規約：底の変換を固定と仮定しない。使われ方：余極限関手と native 比較の整合。

対応節は Kerodon 7.1（Tag 02H1）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
variable {K X : SSet.{u}} {f g : K ⟶ X}
  (c : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone f) (d : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone g) (H : SSet.Homotopy c.val d.val)

/-- 元の二つの余錐の単位円柱を結ぶ、元の全余錐円柱の制限。 -/
def coconeHomotopyUnitCylinder :
    SSet.Homotopy (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationHomotopy c).h
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationHomotopy d).h where
  h := (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeUnitCylinderMap K ▷ (Δ[1] : SSet.{u})) ≫ H.h
  h₀ := by
    rw [SSet.ι₀_comp_assoc, H.h₀, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeTransformationHomotopy_h]
    rfl
  h₁ := by
    rw [SSet.ι₁_comp_assoc, H.h₁, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeTransformationHomotopy_h]
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
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (Δ[0] : SSet.{u}) ▷ Δ[1]) ≫ H.h := by
  have h : SSet.ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeUnitCylinderMap K = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (Δ[0] : SSet.{u}) := by
    let e : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (Δ[0] : SSet.{u})) := ⟨𝟙 _, Category.comp_id _⟩
    have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationHomotopy e).h₀
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeTransformationHomotopy_h, e, Category.comp_id] using he
  change _ ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeUnitCylinderMap K ▷ Δ[1]) ≫ H.h) = _
  rw [← Category.assoc, ← comp_whiskerRight, h]

/-- 単位の二時間の円柱の、頂点側の時間一の制限。 -/
lemma coconeHomotopyUnitCylinder_target :
    (SSet.ι₁ (X := K) ▷ (Δ[1] : SSet.{u})) ≫
      (coconeHomotopyUnitCylinder c d H).h =
        (SSet.const (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K (Δ[0] : SSet.{u}))) ▷ Δ[1]) ≫ H.h := by
  have h : SSet.ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeUnitCylinderMap K =
      SSet.const (SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr K (Δ[0] : SSet.{u}))) := by
    let e : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl K (Δ[0] : SSet.{u})) := ⟨𝟙 _, Category.comp_id _⟩
    have he := (_root_.SerrePositivity.InfinityCategories.Kerodon.TheYonedaEmbedding.TheYonedaEmbedding.coconeTransformationHomotopy e).h₁
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeTransformationHomotopy_h, e, Category.comp_id,
      _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.JoinCocone.vertex_eq] using he
  change _ ≫ ((_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeUnitCylinderMap K ▷ Δ[1]) ≫ H.h) = _
  rw [← Category.assoc, ← comp_whiskerRight, h]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits
