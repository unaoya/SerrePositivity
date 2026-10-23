module

public import SerrePositivity.InfinityCategories.Core.JoinAssociatorBoundary

/-!
概要：join の結合同型は右の二因子全体の包含を厳密に保つ。
方針：空の左因子の切断表示を直接計算する。
規約：全単体での射の等式。使われ方：区間全体を保つ錐の組み替え。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
namespace SerrePositivity.InfinityCategories.F2.Ind

/-- 結合同型は、右の二因子を同じ全包含で写す。 -/
lemma joinAssociator_rightPair (A B C : SSet.{u}) :
    joinMap (joinInr A B) (𝟙 C) ≫ (stableJoinAssociator A B C).hom =
      joinInr A (join B C) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨⟨_ | ℓ, hℓ⟩, x, y⟩
  · refine Join.Simplex.ext _ _ rfl ?_ ?_
    · rfl
    · refine Join.Simplex.ext _ _ rfl ?_ ?_
      · rfl
      · exact Join.augHom_id C _ y
  · refine Join.Simplex.ext _ _ rfl ?_ ?_
    · rfl
    · refine Join.Simplex.ext _ _ rfl ?_ ?_
      · rfl
      · exact Join.augHom_id C _ y

end SerrePositivity.InfinityCategories.F2.Ind
