module
public import Mathlib.CategoryTheory.Functor.Category

/-! # 同型で端点表示を変えた射の自然性

概要：同型で共役した射にも、元の射の比較可換式を移す。
方針：関手の合成保存と同型の打ち消しだけを使う。
規約：任意の圏と関手。使われ方：D7 の cofiber 三角形の頂点表示の変更。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory
variable {C : Type u} [Category C] {D : Type v} [Category D]

/-- 端点を同型で変えた射の関手像の比較。 -/
lemma functor_conjugation_comparison (F : C ⥤ D) {X Y X' Y' : C} {U V : D}
    (eX : X ≅ X') (eY : Y ≅ Y') (vX : F.obj X' ≅ U) (vY : F.obj Y' ≅ V)
    (f : X ⟶ Y) (a : X' ⟶ Y') (b : U ⟶ V)
    (hf : f = eX.hom ≫ a ≫ eY.inv)
    (ha : F.map a ≫ vY.hom = vX.hom ≫ b) :
    F.map f ≫ (F.mapIso eY ≪≫ vY).hom = (F.mapIso eX ≪≫ vX).hom ≫ b := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, Category.assoc]
  calc
    _ = F.map (f ≫ eY.hom) ≫ vY.hom := by rw [F.map_comp, Category.assoc]
    _ = F.map (eX.hom ≫ a) ≫ vY.hom := by
      congr 2
      rw [hf]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = F.map eX.hom ≫ (F.map a ≫ vY.hom) := by rw [F.map_comp, Category.assoc]
    _ = _ := by rw [ha]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
