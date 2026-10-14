module

public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorAssociator
public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorLeftUnit
public import SerrePositivity.CategoryTheory.Monoidal.BalancedTensorRightUnit

/-! # 釣り合いテンソル積のtriangle整合性 -/

@[expose] public section

universe v u

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace SerrePositivity.MonoidalBalancedTensor

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  (M : C) [MonObj M] [IsCommMonObj M] [HasCoequalizers C]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfShape WalkingParallelPair (tensorRight X)]

/-- 結合同型を左単位比較へ続ける経路と、右単位比較を先に行う経路は一致する。 -/
lemma triangle (E F : Mod C M) :
    (associatorIso M E (Mod.regular M) F).hom ≫
        moduleMap M (𝟙 E) (leftUnitIso M F).hom =
      moduleMap M (rightUnitIso M E).hom (𝟙 F) := by
  apply Mod.hom_ext
  apply (cancel_epi (tripleLeftProjection M E (Mod.regular M) F)).1
  change tripleLeftProjection M E (Mod.regular M) F ≫
      associatorHom M E (Mod.regular M) F ≫ map M (𝟙 E) (leftUnitIso M F).hom =
    tripleLeftProjection M E (Mod.regular M) F ≫ map M (rightUnitIso M E).hom (𝟙 F)
  rw [tripleLeftProjection_associatorHom_assoc, tripleRightProjection, Category.assoc,
    projection_map, tripleLeftProjection, Category.assoc, projection_map]
  change (α_ E.X M F.X).hom ≫ E.X ◁ projection M (Mod.regular M) F ≫
      (𝟙 E.X ⊗ₘ leftUnitHom M F) ≫ projection M E F =
    projection M E (Mod.regular M) ▷ F.X ≫
      (rightUnitHom M E ⊗ₘ 𝟙 F.X) ≫ projection M E F
  rw [id_tensorHom, tensorHom_id, ← whiskerLeft_comp_assoc, projection_leftUnitHom,
    ← comp_whiskerRight_assoc, projection_rightUnitHom]
  simpa only [relationLeft, relationRight, Category.assoc] using
    (projection_condition M E F).symm

/-- triangleの両経路を、元の結合順から逆結合同型を介した比較として書く。 -/
lemma triangle_inv (E F : Mod C M) :
    (associatorIso M E (Mod.regular M) F).inv ≫
        moduleMap M (rightUnitIso M E).hom (𝟙 F) =
      moduleMap M (𝟙 E) (leftUnitIso M F).hom := by
  rw [← triangle M E F, Iso.inv_hom_id_assoc]

end SerrePositivity.MonoidalBalancedTensor
