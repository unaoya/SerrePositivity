module

public import SerrePositivity.InfinityCategories.F1.Joins.ConeSpanPointAnodyne
public import SerrePositivity.InfinityCategories.Core.PushoutLegExpansion
public import SerrePositivity.InfinityCategories.Core.ColimitExistenceTransfer

/-!
概要：二つの右余錐を貼った図式の元の底と両余錐を保持する。
方針：元の pushout の両側を順に余錐へ拡大する。
規約：図式と全余錐の制限を厳密な射の等号で回収する。
使われ方：部分余極限の付加による余極限存在の転送。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories
variable {A B C X : SSet.{u}} (i : A ⟶ B) (j : A ⟶ C)

/-- 元の底の pushout から二つの右余錐を貼った形状への指定射。 -/
def coneSpanBaseMap : pushout i j ⟶ coneSpanShape i j :=
  pushoutLeftExpansion i j (joinInl B Δ[0]) ≫
    pushoutRightExpansion (i ≫ joinInl B Δ[0]) j (joinInl C Δ[0])

/-- 底の左部分への制限。 -/
lemma coneSpanBaseMap_left :
    pushout.inl i j ≫ coneSpanBaseMap i j =
      joinInl B Δ[0] ≫ pushout.inl (i ≫ joinInl B Δ[0]) (j ≫ joinInl C Δ[0]) := by
  simp only [coneSpanBaseMap, pushoutLeftExpansion, pushoutRightExpansion,
    pushout.inl_desc_assoc, Category.assoc, pushout.inl_desc]

/-- 底の右部分への制限。 -/
lemma coneSpanBaseMap_right :
    pushout.inr i j ≫ coneSpanBaseMap i j =
      joinInl C Δ[0] ≫ pushout.inr (i ≫ joinInl B Δ[0]) (j ≫ joinInl C Δ[0]) := by
  simp only [coneSpanBaseMap, pushoutLeftExpansion, pushoutRightExpansion,
    pushout.inr_desc_assoc, Category.assoc, pushout.inr_desc]

variable (F : coneSpanShape i j ⟶ X)

/-- 貼り合わせた図式の左側の実余錐。 -/
def coneSpanLeftCocone : JoinCocone
    (joinInl B Δ[0] ≫ (pushout.inl (i ≫ joinInl B Δ[0]) (j ≫ joinInl C Δ[0]) ≫ F)) :=
  ⟨pushout.inl _ _ ≫ F, rfl⟩

/-- 貼り合わせた図式の右側の実余錐。 -/
def coneSpanRightCocone : JoinCocone
    (joinInl C Δ[0] ≫ (pushout.inr (i ≫ joinInl B Δ[0]) (j ≫ joinInl C Δ[0]) ≫ F)) :=
  ⟨pushout.inr _ _ ≫ F, rfl⟩

end SerrePositivity.InfinityCategories
