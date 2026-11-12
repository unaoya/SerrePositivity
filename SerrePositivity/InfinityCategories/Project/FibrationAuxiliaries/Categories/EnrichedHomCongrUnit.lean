module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.EnrichedHomCongrComposition

/-!
概要：元の対象同型による豊穣 Hom の共役は、元の豊穣単位を保つ。
方針：通常の射の豊穣表示と前後合成の整合性で単位の像を計算する。
規約：同じ対象同型と元の通常の射を保持する。
使われ方：全局所 Hom 上の結合共役を豊穣関手へ束ねる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
open CategoryTheory MonoidalCategory
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

variable (V : Type u) [Category.{v} V] [MonoidalCategory V]
  {C : Type w} [Category.{z} C] [EnrichedOrdinaryCategory V C]

/-- 豊穣後合成は、通常の同じ二射の豊穣表示の合成を回収する。 -/
lemma enrichedHomWhiskerLeft_unit {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eHomEquiv V f ≫ eHomWhiskerLeft V X g = eHomEquiv V (f ≫ g) := by
  rw [eHomWhiskerLeft, rightUnitor_inv_naturality_assoc, ← tensorHom_def_assoc,
    ← unitors_inv_equal, ← eHomEquiv_comp]

/-- 豊穣前合成も、通常の同じ二射の豊穣表示の合成を回収する。 -/
lemma enrichedHomWhiskerRight_unit {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    eHomEquiv V g ≫ eHomWhiskerRight V f Z = eHomEquiv V (f ≫ g) := by
  rw [eHomWhiskerRight, leftUnitor_inv_naturality_assoc, ← tensorHom_def'_assoc,
    ← eHomEquiv_comp]

/-- 同じ対象同型による共役は、元の豊穣単位を厳密に保つ。 -/
lemma enrichedHomCongr_identity {X X' : C} (α : X ≅ X') :
    eId V X ≫ (Iso.eHomCongr V α α).hom = eId V X' := by
  rw [← eHomEquiv_id, Iso.eHomCongr_hom, ← Category.assoc,
    enrichedHomWhiskerRight_unit, enrichedHomWhiskerLeft_unit]
  simp

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
