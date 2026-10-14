module

public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorModule
public import Mathlib.Tactic.CategoryTheory.Slice

/-! # 釣り合い商のテンソルによる保存と反復テンソルの標準射 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalBalancedTensor

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  (M : C) [MonObj M] [HasCoequalizers C]

section Right

variable (E F : Mod C M) (X : C)
  [PreservesColimitsOfShape WalkingParallelPair (tensorRight X)]

/-- 右テンソルした商の標準射はエピ射。 -/
instance projection_whiskerRight_epi : Epi (projection M E F ▷ X) :=
  inferInstanceAs (Epi ((tensorRight X).map
    (coequalizer.π (relationLeft M E F) (relationRight M E F))))

/-- 右テンソル後の釣り合い条件を満たす射を、右テンソルした商へ降ろす。 -/
def descRight {Y : C} (f : (E.X ⊗ F.X) ⊗ X ⟶ Y)
    (h : relationLeft M E F ▷ X ≫ f = relationRight M E F ▷ X ≫ f) :
    obj M E F ⊗ X ⟶ Y :=
  (PreservesCoequalizer.iso (tensorRight X) (relationLeft M E F) (relationRight M E F)).inv ≫
    coequalizer.desc f h

/-- 右テンソル後の降下は標準射上で指定した射に一致する。 -/
@[reassoc (attr := simp)] lemma projection_descRight {Y : C} (f : (E.X ⊗ F.X) ⊗ X ⟶ Y)
    (h : relationLeft M E F ▷ X ≫ f = relationRight M E F ▷ X ≫ f) :
    projection M E F ▷ X ≫ descRight M E F X f h = f :=
  map_π_preserves_coequalizer_inv_desc (tensorRight X) _ _ f h

end Right

section Left

variable (X : C) (E F : Mod C M)
  [PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]

/-- 左テンソルした商の標準射はエピ射。 -/
instance projection_whiskerLeft_epi : Epi (X ◁ projection M E F) :=
  inferInstanceAs (Epi ((tensorLeft X).map
    (coequalizer.π (relationLeft M E F) (relationRight M E F))))

/-- 左テンソル後の釣り合い条件を満たす射を、左テンソルした商へ降ろす。 -/
def descLeft {Y : C} (f : X ⊗ (E.X ⊗ F.X) ⟶ Y)
    (h : X ◁ relationLeft M E F ≫ f = X ◁ relationRight M E F ≫ f) :
    X ⊗ obj M E F ⟶ Y :=
  (PreservesCoequalizer.iso (tensorLeft X) (relationLeft M E F) (relationRight M E F)).inv ≫
    coequalizer.desc f h

/-- 左テンソル後の降下は標準射上で指定した射に一致する。 -/
@[reassoc (attr := simp)] lemma projection_descLeft {Y : C} (f : X ⊗ (E.X ⊗ F.X) ⟶ Y)
    (h : X ◁ relationLeft M E F ≫ f = X ◁ relationRight M E F ≫ f) :
    X ◁ projection M E F ≫ descLeft M X E F f h = f :=
  map_π_preserves_coequalizer_inv_desc (tensorLeft X) _ _ f h

end Left

variable [IsCommMonObj M]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]

/-- 標準射は第一因子から得るテンソル加群の作用と両立する。 -/
def projectionModuleHom (E F : Mod C M) : tensorRightObj M E F.X ⟶ moduleObj M E F :=
  Mod.Hom.mk' (projection M E F) (by
    change ((α_ M E.X F.X).inv ≫ γ[M,E.X] ▷ F.X) ≫ projection M E F =
      M ◁ projection M E F ≫ γ[M,(moduleObj M E F).X]
    rw [Category.assoc, projection_action])

/-- 商の右作用を、第二因子の右作用と標準射で計算する。 -/
@[reassoc] lemma projection_rightAction (E F : Mod C M) :
    projection M E F ▷ M ≫ rightActionMap M (moduleObj M E F) =
      (α_ E.X F.X M).hom ≫ E.X ◁ rightActionMap M F ≫ projection M E F := by
  rw [rightActionMap]
  erw [BraidedCategory.braiding_naturality_left_assoc, projection_action]
  rw [BraidedCategory.braiding_tensor_left_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  slice_lhs 4 5 => rw [← comp_whiskerRight]
  change (α_ E.X F.X M).hom ≫ E.X ◁ (β_ F.X M).hom ≫ (α_ E.X M F.X).inv ≫
      rightActionMap M E ▷ F.X ≫ projection M E F = _
  have h := projection_condition M E F
  change rightActionMap M E ▷ F.X ≫ projection M E F =
    ((α_ E.X M F.X).hom ≫ E.X ◁ γ[M,F.X]) ≫ projection M E F at h
  rw [h, Category.assoc, Iso.inv_hom_id_assoc]
  simp only [rightActionMap, whiskerLeft_comp, Category.assoc]

/-- 左結合した三重テンソルへの、三つの因子からの標準射。 -/
def tripleLeftProjection (E F G : Mod C M) :
    (E.X ⊗ F.X) ⊗ G.X ⟶ obj M (moduleObj M E F) G :=
  projection M E F ▷ G.X ≫ projection M (moduleObj M E F) G

/-- 右結合した三重テンソルへの、三つの因子からの標準射。 -/
def tripleRightProjection (E F G : Mod C M) :
    E.X ⊗ (F.X ⊗ G.X) ⟶ obj M E (moduleObj M F G) :=
  E.X ◁ projection M F G ≫ projection M E (moduleObj M F G)

/-- 右結合した三重テンソルの標準射はエピ射。 -/
instance tripleRightProjection_epi (E F G : Mod C M) :
    Epi (tripleRightProjection M E F G) := by
  unfold tripleRightProjection
  infer_instance

/-- 左結合の標準射は三つの加群の射と両立する。 -/
@[reassoc] lemma tripleLeftProjection_map {E E' F F' G G' : Mod C M}
    (f : E ⟶ E') (g : F ⟶ F') (h : G ⟶ G') :
    tripleLeftProjection M E F G ≫ map M (moduleMap M f g) h =
      ((f.hom ⊗ₘ g.hom) ⊗ₘ h.hom) ≫ tripleLeftProjection M E' F' G' := by
  rw [tripleLeftProjection, Category.assoc, projection_map]
  change projection M E F ▷ G.X ≫ (map M f g ⊗ₘ h.hom) ≫
    projection M (moduleObj M E' F') G' = _
  simp only [tensorHom_def, Category.assoc]
  rw [← comp_whiskerRight_assoc, projection_map, comp_whiskerRight, Category.assoc,
    ← whisker_exchange_assoc]
  simp only [tripleLeftProjection, tensorHom_def]

/-- 右結合の標準射は三つの加群の射と両立する。 -/
@[reassoc] lemma tripleRightProjection_map {E E' F F' G G' : Mod C M}
    (f : E ⟶ E') (g : F ⟶ F') (h : G ⟶ G') :
    tripleRightProjection M E F G ≫ map M f (moduleMap M g h) =
      (f.hom ⊗ₘ (g.hom ⊗ₘ h.hom)) ≫ tripleRightProjection M E' F' G' := by
  rw [tripleRightProjection, Category.assoc, projection_map]
  change E.X ◁ projection M F G ≫ (f.hom ⊗ₘ map M g h) ≫
    projection M E' (moduleObj M F' G') = _
  simp only [tensorHom_def', Category.assoc]
  rw [← whiskerLeft_comp_assoc, projection_map, whiskerLeft_comp, Category.assoc,
    whisker_exchange_assoc]
  simp only [tripleRightProjection, tensorHom_def']

variable [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)]

/-- 左結合した三重テンソルの標準射はエピ射。 -/
instance tripleLeftProjection_epi (E F G : Mod C M) :
    Epi (tripleLeftProjection M E F G) := by
  unfold tripleLeftProjection
  infer_instance

end SerrePositivity.MonoidalBalancedTensor
