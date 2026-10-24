module

public import SerrePositivity.InfinityCategories.Core.PrecompositionLifting
public import SerrePositivity.InfinityCategories.Core.EquivalenceCylinderFunctorIso
public import SerrePositivity.InfinityCategories.Core.RelativeEquivalenceCylinder
/-!
概要：可逆な境界修正を、別の全固定境界を保って単射へ延長する。
方針：変更側の可逆円柱と固定側の定値円柱を pushout で貼り、同じ単射へ延長する。
規約：固定側を途中で忘れず、全写像の厳密な一致を結論する。
使われ方：指定始点評価を保つ余錐比較の相対反映。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2.Ind
/-- 概要：可逆修正を単射へ延長し、共通部分で一致する別の境界を厳密に固定する。
方針：二つの円柱を貼って既存の延長を使う。規約：固定全境界を保持。使われ方：相対反映。 -/
lemma exists_extension_of_equivalenceFamily_fixed_boundary
    {A B C D Q X : SSet.{u}} [Quasicategory X]
    {i : A ⟶ B} {j : A ⟶ C} {r : B ⟶ D} {s : C ⟶ D}
    (hP : IsPushout i j r s) (t : D ⟶ Q) [Mono t] (u : Q ⟶ X) (v : B ⟶ X)
    (hv : i ≫ v = j ≫ s ≫ t ≫ u)
    (V : B ⊗ equivalenceInterval ⟶ X)
    (h₀ : equivalenceCylinderEndpoint B false ≫ V = r ≫ t ≫ u)
    (h₁ : equivalenceCylinderEndpoint B true ≫ V = v)
    (hV : (i ▷ equivalenceInterval) ≫ V = fst A equivalenceInterval ≫ j ≫ s ≫ t ≫ u) :
    ∃ F : Q ⟶ X, r ≫ t ≫ F = v ∧ s ≫ t ≫ F = s ≫ t ≫ u := by
  let w := hP.desc v (s ≫ t ≫ u) hv
  let R := fst C equivalenceInterval ≫ s ≫ t ≫ u
  have hc : (i ▷ equivalenceInterval) ≫ V = (j ▷ equivalenceInterval) ≫ R := by
    rw [hV]
    dsimp only [R]
    rw [← Category.assoc (j ▷ equivalenceInterval), whiskerRight_fst, Category.assoc]
  let W := (hP.map (tensorRight equivalenceInterval)).desc V R hc
  have W₀ : equivalenceCylinderEndpoint D false ≫ W = t ≫ u := by
    apply hP.hom_ext
    · rw [← Category.assoc, equivalenceCylinderEndpoint_naturality, Category.assoc,
        IsPushout.inl_desc, h₀]
    · rw [← Category.assoc, equivalenceCylinderEndpoint_naturality, Category.assoc,
        IsPushout.inr_desc]
      dsimp only [R]
      rw [← Category.assoc, equivalenceCylinderEndpoint_fst, Category.id_comp]
  have W₁ : equivalenceCylinderEndpoint D true ≫ W = w := by
    apply hP.hom_ext
    · rw [← Category.assoc, equivalenceCylinderEndpoint_naturality, Category.assoc,
        IsPushout.inl_desc, h₁]
      exact (hP.inl_desc _ _ _).symm
    · rw [← Category.assoc, equivalenceCylinderEndpoint_naturality, Category.assoc,
        IsPushout.inr_desc]
      dsimp only [R]
      rw [← Category.assoc, equivalenceCylinderEndpoint_fst, Category.id_comp]
      exact (hP.inr_desc _ _ _).symm
  obtain ⟨e⟩ := nonempty_functorIso_of_equivalenceCylinder_extension W W₀ W₁
  obtain ⟨F, hF⟩ := exists_extension_of_functorIso t u w e
  refine ⟨F, ?_, ?_⟩
  · rw [hF]
    exact hP.inl_desc _ _ _
  · rw [hF]
    exact hP.inr_desc _ _ _
end SerrePositivity.InfinityCategories.F2.Ind
