module
public import SerrePositivity.InfinityCategories.Core.FatJoin
public import SerrePositivity.InfinityCategories.Core.FatJoinComparison
public import SerrePositivity.InfinityCategories.Core.FatJoinTensorExt
public import SerrePositivity.InfinityCategories.Core.Join
public import SerrePositivity.InfinityCategories.Core.JoinCylinderSimplex
public import SerrePositivity.InfinityCategories.Core.JoinTensor
public import SerrePositivity.InfinityCategories.Core.JoinTensorRight
public import SerrePositivity.InfinityCategories.Core.FatJoinRightTensor

/-! # 余錐の直積比較の整合性

概要：fat join の右直積比較は通常の join の右直積比較と可換。
方針：円柱と両因子で比較し、区間の切断で直積成分を制限する。
規約：全ての単体集合は任意。使われ方：coslice 比較と余錐の族の比較の同定。
-/
@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：fat join と通常の join の右直積比較は比較射と可換。
方針：円柱では同じ区間の切断の右側へ二つの直積成分を制限する。
規約：quasicategory 性は不要。使われ方：余錐の二つの比較射の一致。 -/
lemma stableFatJoinTensorRight_comparison (A B P : SSet.{u}) :
    stableFatJoinTensorRight A B P ≫ fatJoinComparison A (B ⊗ P) =
      (fatJoinComparison A B ▷ P) ≫ joinTensorRight A B P := by
  apply fatJoin_tensorRight_hom_ext
  · have hs : (fatJoinCylinder A B ▷ P) ≫ (fatJoinComparison A B ▷ P) =
        (joinCylinderMap A B ▷ P) := by rw [← comp_whiskerRight, fatJoinCylinder_comparison]
    rw [← Category.assoc (fatJoinCylinder A B ▷ P), stableFatJoinTensorRight_cylinder]
    simp only [Category.assoc, fatJoinCylinder_comparison]
    rw [← Category.assoc (fatJoinCylinder A B ▷ P), hs]
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨⟨⟨a, t⟩, b⟩, p⟩
    change (joinCylinderMap A (B ⊗ P)).app (Opposite.op ⦋n⦌) ((a, t), (b, p)) =
      Join.tensorRightSimplex A B P n ((joinCylinderMap A B).app (Opposite.op ⦋n⦌) ((a, t), b)) p
    rw [joinCylinderMap_app, joinCylinderMap_app]
    dsimp only [Join.tensorRightSimplex]
    refine Join.Simplex.ext _ _ ?_ ?_ ?_
    · rfl
    · rfl
    · exact Join.augTensorEquiv_symm_augMap B P _ _ _
  · rw [← Category.assoc (fatJoinInl A B ▷ P), stableFatJoinTensorRight_inl]
    simp only [Category.assoc, fatJoinInl_comparison]
    have hs : (fatJoinInl A B ▷ P) ≫ (fatJoinComparison A B ▷ P) = (joinInl A B ▷ P) := by
      rw [← comp_whiskerRight, fatJoinInl_comparison]
    rw [← Category.assoc, hs, joinTensorRight_inl]
  · rw [← Category.assoc (fatJoinInr A B ▷ P), stableFatJoinTensorRight_inr,
      fatJoinInr_comparison]
    have hs : (fatJoinInr A B ▷ P) ≫ (fatJoinComparison A B ▷ P) = (joinInr A B ▷ P) := by
      rw [← comp_whiskerRight, fatJoinInr_comparison]
    rw [← Category.assoc, hs, joinTensorRight_inr]

end SerrePositivity.InfinityCategories
