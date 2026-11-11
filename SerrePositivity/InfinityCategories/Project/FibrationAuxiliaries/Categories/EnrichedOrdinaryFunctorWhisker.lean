module

public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories.EnrichedHomCongrUnit

/-!
概要：元の豊穣関手は、通常の射による全高次 Hom の前後合成を保つ。
方針：通常の射の豊穣表示と、元の豊穣単位・合成の保存を使う。
規約：通常の射と全高次の豊穣作用を選び直さない。
使われ方：指定された同型の豊穣共役を分類後の自然な比較へ移す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z w' z'
open CategoryTheory MonoidalCategory
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

variable (V : Type u) [Category.{v} V] [MonoidalCategory V]
  {C : Type w} [Category.{z} C] [EnrichedOrdinaryCategory V C]
  {D : Type w'} [Category.{z'} D] [EnrichedOrdinaryCategory V D]

/-- 元の豊穣関手に対応する、元の通常の射の豊穣表示を保つ通常の関手。 -/
def enrichedOrdinaryFunctor (F : EnrichedFunctor V C D) : C ⥤ D :=
  ForgetEnrichment.equivInverse V C ⋙ F.forget ⋙ ForgetEnrichment.equivFunctor V D

/-- 同じ通常の関手の像は、元の豊穣表示に同じ Hom 作用を続けたもの。 -/
lemma enrichedOrdinaryFunctor_map_unit (F : EnrichedFunctor V C D) {X Y : C} (f : X ⟶ Y) :
    eHomEquiv V ((enrichedOrdinaryFunctor V F).map f) = eHomEquiv V f ≫ F.map X Y :=
  (eHomEquiv V).apply_symm_apply _

/-- 豊穣関手は、通常の射による全高次 Hom の後合成を厳密に保つ。 -/
lemma enrichedOrdinaryFunctor_whiskerLeft
    (F : EnrichedFunctor V C D) (X : C) {Y Z : C} (f : Y ⟶ Z) :
    eHomWhiskerLeft V X f ≫ F.map X Z =
      F.map X Y ≫ eHomWhiskerLeft V (F.obj X) ((enrichedOrdinaryFunctor V F).map f) := by
  simp only [eHomWhiskerLeft, Category.assoc]
  rw [F.map_comp, whiskerLeft_comp_tensorHom_assoc,
    ← enrichedOrdinaryFunctor_map_unit, rightUnitor_inv_comp_tensorHom_assoc]
  rfl

/-- 豊穣関手は、通常の射による全高次 Hom の前合成も厳密に保つ。 -/
lemma enrichedOrdinaryFunctor_whiskerRight
    (F : EnrichedFunctor V C D) {X Y : C} (f : X ⟶ Y) (Z : C) :
    eHomWhiskerRight V f Z ≫ F.map X Z =
      F.map Y Z ≫ eHomWhiskerRight V ((enrichedOrdinaryFunctor V F).map f) (F.obj Z) := by
  simp only [eHomWhiskerRight, Category.assoc]
  rw [F.map_comp, whiskerRight_comp_tensorHom_assoc,
    ← enrichedOrdinaryFunctor_map_unit, leftUnitor_inv_comp_tensorHom_assoc]
  rfl

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
