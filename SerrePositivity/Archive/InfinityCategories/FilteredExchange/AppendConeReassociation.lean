module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.JoinAssociatorBoundary

/-!
概要：追加錐の二終点を一つの実辺へ束ねるための join の組み替え。
方針：元の結合同型の自然性と、右二因子全体の包含を計算する。
規約：各点の同値でなく全図式の等式。使われ方：指定射上の slice の固定条件。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- join の右二因子全体は、同じ結合同型で元の全包含へ移る。 -/
lemma appendConeAssociator_rightPair (A B C : SSet.{u}) :
    joinMap (joinInr A B) (𝟙 C) ≫ (stableJoinAssociator A B C).hom =
      joinInr A (join B C) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨_ | ℓ, hℓ⟩, x, y⟩
  all_goals
    refine Join.Simplex.ext _ _ rfl ?_ ?_
    · rfl
    · refine Join.Simplex.ext _ _ rfl ?_ ?_
      · rfl
      · exact Join.augHom_id C _ y

/-- 結合同型の逆は、元の右二因子全体をそのまま保持する。 -/
lemma appendConeAssociator_rightPair_inv (A B C : SSet.{u}) :
    joinInr A (join B C) ≫ (stableJoinAssociator A B C).inv =
      joinMap (joinInr A B) (𝟙 C) := by
  rw [← appendConeAssociator_rightPair, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

/-- 結合同型の逆も、元の左因子の全写像に厳密に自然。 -/
lemma appendConeAssociator_inv_naturality {A A' B C : SSet.{u}} (f : A ⟶ A') :
    joinMap f (𝟙 (join B C)) ≫ (stableJoinAssociator A' B C).inv =
      (stableJoinAssociator A B C).inv ≫ joinMap (joinMap f (𝟙 B)) (𝟙 C) := by
  have h := congrArg (fun k => (stableJoinAssociator A B C).inv ≫ k ≫
    (stableJoinAssociator A' B C).inv) (stableJoinAssociator_naturality f (𝟙 B) (𝟙 C))
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Iso.inv_hom_id_assoc,
    Iso.hom_inv_id, Category.comp_id, joinMap_id] using h.symm

end SerrePositivity.InfinityCategories.F2
