module

public import SerrePositivity.InfinityCategories.F2.Ind.ConeTensorCorner

/-!
概要：一般の補間領域を、元の試験形状の射で制限する。
方針：元の二境界を pushout の普遍性で写し、元の積への包含と照合する。
規約：両全境界を保持し、試験形状の単射は同じ補間領域の単射へ移す。
使われ方：相対的な終点余錐の延長で元の旧族の全円柱を固定する。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
variable {A B : SSet.{u}} (f : A ⟶ B) (L : SSet.{u})
/-- 概要：元の試験形状の射を、同じ補間領域へ写す。
方針：元の pushout の普遍性。規約：全射の等号。使われ方：旧族を固定した再構成。 -/
def coneTensorCornerMap : coneTensorCorner A L ⟶ coneTensorCorner B L :=
  pushout.desc
    ((f ▷ join L (Δ[0] : SSet.{u})) ≫
      pushout.inl (B ◁ joinInl L (Δ[0] : SSet.{u})) (joinInl B Δ[0] ▷ L))
    ((joinMap f (𝟙 (Δ[0] : SSet.{u})) ▷ L) ≫
      pushout.inr (B ◁ joinInl L (Δ[0] : SSet.{u})) (joinInl B Δ[0] ▷ L)) (by
      rw [← Category.assoc, whisker_exchange f (joinInl L (Δ[0] : SSet.{u})),
        Category.assoc, pushout.condition]
      simp only [← Category.assoc, ← comp_whiskerRight, joinInl_joinMap])
/-- 概要：元の試験族側の全制限を回収する。
方針：元の pushout の普遍性。規約：全射の等号。使われ方：旧族を固定した再構成。 -/
lemma coneTensorCornerMap_old :
    pushout.inl (A ◁ joinInl L (Δ[0] : SSet.{u})) (joinInl A Δ[0] ▷ L) ≫
      coneTensorCornerMap f L = (f ▷ join L (Δ[0] : SSet.{u})) ≫
        pushout.inl (B ◁ joinInl L (Δ[0] : SSet.{u})) (joinInl B Δ[0] ▷ L) :=
  pushout.inl_desc _ _ _
/-- 概要：下方余錐側の全制限を回収する。
方針：元の pushout の普遍性。規約：全射の等号。使われ方：旧族を固定した再構成。 -/
lemma coneTensorCornerMap_lower :
    pushout.inr (A ◁ joinInl L (Δ[0] : SSet.{u})) (joinInl A Δ[0] ▷ L) ≫
      coneTensorCornerMap f L = (joinMap f (𝟙 (Δ[0] : SSet.{u})) ▷ L) ≫
        pushout.inr (B ◁ joinInl L (Δ[0] : SSet.{u})) (joinInl B Δ[0] ▷ L) :=
  pushout.inr_desc _ _ _
/-- 概要：補間領域の射は元の積への包含と厳密に可換。
方針：元の pushout の普遍性。規約：全射の等号。使われ方：旧族を固定した再構成。 -/
lemma coneTensorCornerInclusion_naturality :
    coneTensorCornerMap f L ≫ coneTensorCornerInclusion B L =
      coneTensorCornerInclusion A L ≫
        (joinMap f (𝟙 (Δ[0] : SSet.{u})) ▷ join L (Δ[0] : SSet.{u})) := by
  apply pushout.hom_ext
  · simp only [← Category.assoc, coneTensorCornerMap_old, coneTensorCornerInclusion_old]
    rw [Category.assoc, coneTensorCornerInclusion_old,
      ← comp_whiskerRight, ← comp_whiskerRight, joinInl_joinMap]
  · simp only [← Category.assoc, coneTensorCornerMap_lower, coneTensorCornerInclusion_lower]
    rw [Category.assoc, coneTensorCornerInclusion_lower]
    exact (whisker_exchange (joinMap f (𝟙 (Δ[0] : SSet.{u})))
      (joinInl L (Δ[0] : SSet.{u}))).symm
/-- 概要：元の試験形状の単射は同じ補間領域の単射になる。
方針：元の pushout の普遍性。規約：全射の等号。使われ方：旧族を固定した再構成。 -/
instance coneTensorCornerMap_mono [Mono f] : Mono (coneTensorCornerMap f L) := by
  have : Mono (joinMap f (𝟙 (Δ[0] : SSet.{u})) ▷ join L (Δ[0] : SSet.{u})) :=
    (tensorRight _).map_mono _
  exact mono_of_mono_fac (coneTensorCornerInclusion_naturality f L)
end SerrePositivity.InfinityCategories.F2.Ind
