module

public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorAssociator
public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorSymmetry

/-! # 釣り合いテンソル積のhexagon整合性 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalBalancedTensor

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]
  (M : C) [MonObj M] [IsCommMonObj M] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]

/-- 右結合の三因子の標準射の外側の交換を計算する。 -/
@[reassoc] lemma tripleRightProjection_swap (E F G : Mod C M) :
    tripleRightProjection M E F G ≫ swapHom M E (moduleObj M F G) =
      (β_ E.X (F.X ⊗ G.X)).hom ≫ tripleLeftProjection M F G E := by
  rw [tripleRightProjection, Category.assoc, projection_swapHom]
  erw [BraidedCategory.braiding_naturality_right_assoc]
  rfl

/-- 左結合の三因子の標準射の外側の交換を計算する。 -/
@[reassoc] lemma tripleLeftProjection_swap (E F G : Mod C M) :
    tripleLeftProjection M E F G ≫ swapHom M (moduleObj M E F) G =
      (β_ (E.X ⊗ F.X) G.X).hom ≫ tripleRightProjection M G E F := by
  rw [tripleLeftProjection, Category.assoc, projection_swapHom]
  erw [BraidedCategory.braiding_naturality_left_assoc]
  rfl

/-- 左結合の三因子の標準射の内側の交換を計算する。 -/
@[reassoc] lemma tripleLeftProjection_map_swap (E F G : Mod C M) :
    tripleLeftProjection M E F G ≫ map M (swapIso M E F).hom (𝟙 G) =
      (β_ E.X F.X).hom ▷ G.X ≫ tripleLeftProjection M F E G := by
  rw [tripleLeftProjection, Category.assoc, projection_map]
  change projection M E F ▷ G.X ≫ (swapHom M E F ⊗ₘ 𝟙 G.X) ≫
    projection M (moduleObj M F E) G = _
  rw [tensorHom_id, ← comp_whiskerRight_assoc, projection_swapHom, comp_whiskerRight]
  simp only [tripleLeftProjection, Category.assoc]

/-- 右結合の三因子の標準射の内側の交換を計算する。 -/
@[reassoc] lemma tripleRightProjection_map_swap (E F G : Mod C M) :
    tripleRightProjection M E F G ≫ map M (𝟙 E) (swapIso M F G).hom =
      E.X ◁ (β_ F.X G.X).hom ≫ tripleRightProjection M E G F := by
  rw [tripleRightProjection, Category.assoc, projection_map]
  change E.X ◁ projection M F G ≫ (𝟙 E.X ⊗ₘ swapHom M F G) ≫
    projection M E (moduleObj M G F) = _
  rw [id_tensorHom, ← whiskerLeft_comp_assoc, projection_swapHom, whiskerLeft_comp]
  simp only [tripleRightProjection, Category.assoc]

variable [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)]

/-- 釣り合いテンソル積の結合・交換同型は順方向のhexagonを満たす。 -/
lemma hexagon_forward (E F G : Mod C M) :
    (associatorIso M E F G).hom ≫ (swapIso M E (moduleObj M F G)).hom ≫
        (associatorIso M F G E).hom =
      moduleMap M (swapIso M E F).hom (𝟙 G) ≫ (associatorIso M F E G).hom ≫
        moduleMap M (𝟙 F) (swapIso M E G).hom := by
  apply Mod.hom_ext
  apply (cancel_epi (tripleLeftProjection M E F G)).1
  change tripleLeftProjection M E F G ≫ associatorHom M E F G ≫
      swapHom M E (moduleObj M F G) ≫ associatorHom M F G E =
    tripleLeftProjection M E F G ≫ map M (swapIso M E F).hom (𝟙 G) ≫
      associatorHom M F E G ≫ map M (𝟙 F) (swapIso M E G).hom
  rw [tripleLeftProjection_associatorHom_assoc, tripleRightProjection_swap_assoc,
    tripleLeftProjection_associatorHom, tripleLeftProjection_map_swap_assoc,
    tripleLeftProjection_associatorHom_assoc, tripleRightProjection_map_swap,
    BraidedCategory.hexagon_forward_assoc]

/-- 釣り合いテンソル積の結合・交換同型は逆方向のhexagonを満たす。 -/
lemma hexagon_reverse (E F G : Mod C M) :
    (associatorIso M E F G).inv ≫ (swapIso M (moduleObj M E F) G).hom ≫
        (associatorIso M G E F).inv =
      moduleMap M (𝟙 E) (swapIso M F G).hom ≫ (associatorIso M E G F).inv ≫
        moduleMap M (swapIso M E G).hom (𝟙 F) := by
  apply Mod.hom_ext
  apply (cancel_epi (tripleRightProjection M E F G)).1
  change tripleRightProjection M E F G ≫ associatorInv M E F G ≫
      swapHom M (moduleObj M E F) G ≫ associatorInv M G E F =
    tripleRightProjection M E F G ≫ map M (𝟙 E) (swapIso M F G).hom ≫
      associatorInv M E G F ≫ map M (swapIso M E G).hom (𝟙 F)
  rw [tripleRightProjection_associatorInv_assoc, tripleLeftProjection_swap_assoc,
    tripleRightProjection_associatorInv, tripleRightProjection_map_swap_assoc,
    tripleRightProjection_associatorInv_assoc, tripleLeftProjection_map_swap,
    BraidedCategory.hexagon_reverse_assoc]

end SerrePositivity.MonoidalBalancedTensor
