module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.FunctorComparisons.EnrichedFunctors.EnrichedMiddleComposition
/-!
概要：豊穣恒等射を閉射で前後合成すると、同じ閉射の豊穣像を得る。
方針：単位子の自然性と通常射の豊穣合成公式を使う。
規約：任意の豊穣通常圏。使われ方：出力分解の実単位の比較差の消滅。
-/
@[expose] public section
universe u v w z
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory
variable (V : Type u) [Category.{v} V] [MonoidalCategory V]
  (C : Type w) [Category.{z} C] [EnrichedOrdinaryCategory V C]
/-- 閉射を恒等豊穣射へ後合成すると、その閉射の豊穣像。 -/
lemma enrichedIdentity_postcompose {X Y : C} (f : X ⟶ Y) :
    eId V X ≫ eHomWhiskerLeft V X f = eHomEquiv V f := by
  rw [eHomWhiskerLeft, ← eHomEquiv_id, ← Category.assoc,
    rightUnitor_inv_naturality]
  rw [Category.assoc, ← tensorHom_def_assoc,
    ← unitors_inv_equal, ← eHomEquiv_comp, Category.id_comp]
/-- 閉射を恒等豊穣射へ前合成しても、その閉射の豊穣像。 -/
lemma enrichedIdentity_precompose {X Y : C} (f : X ⟶ Y) :
    eId V Y ≫ eHomWhiskerRight V f Y = eHomEquiv V f := by
  rw [eHomWhiskerRight, ← eHomEquiv_id, ← Category.assoc,
    leftUnitor_inv_naturality]
  rw [Category.assoc, ← tensorHom_def'_assoc,
    ← eHomEquiv_comp, Category.comp_id]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
