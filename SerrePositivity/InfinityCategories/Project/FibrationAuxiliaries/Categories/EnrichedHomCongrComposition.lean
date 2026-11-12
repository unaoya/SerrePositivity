module

public import Mathlib.CategoryTheory.Enriched.HomCongr

/-!
概要：元の対象の同型による豊穣 Hom の共役は、全高次の豊穣合成を保つ。
方針：前後合成を外へ移し、中間の同型と逆同型を消去する。
規約：通常の射の零単体だけに限定しない。
使われ方：全局所 Hom 上で結合共役を豊穣関手に束ねる。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
open CategoryTheory MonoidalCategory
namespace SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories

/-- 同じ対象同型による共役は、全ての高次の Hom の豊穣合成を厳密に保つ。 -/
lemma enrichedHomCongr_comp_all
    (V : Type u) [Category.{v} V] [MonoidalCategory V]
    {C : Type w} [Category.{z} C] [EnrichedOrdinaryCategory V C]
    {X Y Z X' Y' Z' : C} (α : X ≅ X') (β : Y ≅ Y') (γ : Z ≅ Z') :
    ((Iso.eHomCongr V α β).hom ⊗ₘ (Iso.eHomCongr V β γ).hom) ≫ eComp V X' Y' Z' =
      eComp V X Y Z ≫ (Iso.eHomCongr V α γ).hom := by
  simp only [Iso.eHomCongr_hom, tensorHom_def, comp_whiskerRight,
    MonoidalCategory.whiskerLeft_comp, Category.assoc]
  rw [← eComp_eHomWhiskerLeft, eHom_whisker_cancel_assoc,
    ← eComp_eHomWhiskerRight_assoc]

/-- 同じ共役を始域同型で戻すと、終域同型による元の後合成になる。 -/
lemma enrichedHomCongr_naturality
    (V : Type u) [Category.{v} V] [MonoidalCategory V]
    {C : Type w} [Category.{z} C] [EnrichedOrdinaryCategory V C]
    {X Y X' Y' : C} (α : X ≅ X') (β : Y ≅ Y') :
    (Iso.eHomCongr V α β).hom ≫ eHomWhiskerRight V α.hom Y' =
      eHomWhiskerLeft V X β.hom := by
  rw [Iso.eHomCongr_hom, Category.assoc, eHom_whisker_exchange,
    ← Category.assoc, ← eHomWhiskerRight_comp]
  simp

end SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.Categories
