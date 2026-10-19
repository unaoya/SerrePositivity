module

public import SerrePositivity.InfinityCategories.F2.TensorConeComponentCriterion
public import SerrePositivity.InfinityCategories.F2.ConeValEquality

/-!
概要：直積内の錐の成分の像から直積関手による像の極限性を得る。
方針：元の二射影と直積射の可換式で像の錐を照合する。
規約：元の錐の射と関手 f・g を保持する。
使われ方：lax pullback の両入力の像の極限錐。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
namespace SerrePositivity.InfinityCategories.F2

/-- 概要：各成分の像が極限錐なら直積関手による全体の像も極限錐。
方針：二射影と直積関手の交換式で成分の極限性を全体へ戻す。
規約：始域の二圏の quasicategory 性や錐の極限性は要求しない。
使われ方：選んだ両入力の錐の共通の底への像。 -/
lemma isLimitCone_tensorHom_of_component_images {J X Y X' Y' : SSet.{u}}
    [Quasicategory X'] [Quasicategory Y'] (f : X ⟶ X') (g : Y ⟶ Y')
    {r : J ⟶ X ⊗ Y} (c : JoinCone r)
    (hf : IsLimitCone (mapJoinCone f (mapJoinCone (fst X Y) c)))
    (hg : IsLimitCone (mapJoinCone g (mapJoinCone (snd X Y) c))) :
    IsLimitCone (mapJoinCone (f ⊗ₘ g) c) := by
  apply isLimitCone_tensor_of_components
  · apply (isLimitCone_iff_of_cone_val_eq _ _ ?_).2 hf
    change (c.val ≫ (f ⊗ₘ g)) ≫ fst X' Y' = (c.val ≫ fst X Y) ≫ f
    simp only [Category.assoc, tensorHom_fst]
  · apply (isLimitCone_iff_of_cone_val_eq _ _ ?_).2 hg
    change (c.val ≫ (f ⊗ₘ g)) ≫ snd X' Y' = (c.val ≫ snd X Y) ≫ g
    simp only [Category.assoc, tensorHom_snd]

end SerrePositivity.InfinityCategories.F2
