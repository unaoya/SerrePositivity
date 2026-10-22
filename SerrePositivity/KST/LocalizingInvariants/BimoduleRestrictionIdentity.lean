module

public import SerrePositivity.KST.LocalizingInvariants.BimoduleRestriction

/-!
概要：恒等底射による双加群制限を、underlying 恒等射の実同型で元へ戻す。
方針：左右作用の恒等 whisker を簡約する。
規約：元の双加群を取り替えない。使われ方：同じ底上の制限正方形射の接続。
-/

@[expose] public section
noncomputable section
universe u v
open CategoryTheory MonoidalCategory
namespace SerrePositivity.KST.LocalizingInvariants
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] {A : Mon C} (M : Bimod A A)

def bimoduleRestrictionIdIso : bimoduleRestrict (𝟙 A) M ≅ M := by
  refine Bimod.isoOfIso (Iso.refl M.X) ?_ ?_
  · change ((𝟙 A.X ▷ M.X) ≫ M.actLeft) ≫ 𝟙 M.X = (A.X ◁ 𝟙 M.X) ≫ M.actLeft
    simp only [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id]
  · change ((M.X ◁ 𝟙 A.X) ≫ M.actRight) ≫ 𝟙 M.X = (𝟙 M.X ▷ A.X) ≫ M.actRight
    simp only [id_whiskerRight, whiskerLeft_id, Category.id_comp, Category.comp_id]

lemma bimoduleRestrictionIdIso_hom : (bimoduleRestrictionIdIso M).hom.hom = 𝟙 M.X := rfl

end SerrePositivity.KST.LocalizingInvariants
