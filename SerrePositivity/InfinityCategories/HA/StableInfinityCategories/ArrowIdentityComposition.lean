module
public import Mathlib.CategoryTheory.Comma.Arrow

/-! # Arrow 表示での恒等成分の打ち消し

概要：端点表示の異なる恒等射成分を、合成した Arrow の等式で打ち消す。
方針：Arrow の左右の射影で対象の等式を回収し、同じ Hom の等式へ戻す。
規約：任意の圏。使われ方：D7 の四角形比較の成分の合成。
-/
@[expose] public section
universe u v
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories
open CategoryTheory
variable {C : Type u} [Category.{v} C]

/-- Arrow として恒等射に等しければ、自分の始点の恒等射とも等しい。 -/
lemma arrowMk_eq_id_source {X Y W : C} (f : X ⟶ Y)
    (hf : Arrow.mk f = Arrow.mk (𝟙 W)) : Arrow.mk f = Arrow.mk (𝟙 X) := by
  have hx : X = W := congrArg Arrow.left hf
  cases hx
  exact hf

/-- Arrow として恒等射に等しい左因子は合成から取り除ける。 -/
lemma arrowMk_comp_of_left_identity {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : Arrow.mk f = Arrow.mk (𝟙 W)) : Arrow.mk (f ≫ g) = Arrow.mk g := by
  have hx : X = W := congrArg Arrow.left hf
  have hy : Y = W := congrArg Arrow.right hf
  cases hx
  cases hy
  have h : f = 𝟙 _ := Arrow.mk_injective _ _ hf
  rw [h, Category.id_comp]

/-- Arrow として恒等射に等しい右因子は合成から取り除ける。 -/
lemma arrowMk_comp_of_right_identity {X Y Z W : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : Arrow.mk g = Arrow.mk (𝟙 W)) : Arrow.mk (f ≫ g) = Arrow.mk f := by
  have hy : Y = W := congrArg Arrow.left hg
  have hz : Z = W := congrArg Arrow.right hg
  cases hy
  cases hz
  have h : g = 𝟙 _ := Arrow.mk_injective _ _ hg
  rw [h, Category.comp_id]

/-- 対象の等式による輸送を関手で写した射は Arrow として恒等射。 -/
lemma arrowMk_map_eqToHom {D : Type*} [Category D] (F : C ⥤ D) {X Y : C} (h : X = Y) :
    Arrow.mk (F.map (eqToHom h)) = Arrow.mk (𝟙 (F.obj X)) := by
  cases h
  rw [eqToHom_refl, F.map_id]

/-- 対象の輸送を関手で写した左因子を直接消す。 -/
lemma arrowMk_map_eqToHom_comp {D : Type*} [Category D] (F : C ⥤ D)
    {X Y Z : C} (h : X = Y) (g : Y ⟶ Z) :
    Arrow.mk (F.map (eqToHom h) ≫ F.map g) = Arrow.mk (F.map g) := by
  cases h
  simp

/-- 対象の輸送を関手で写した右因子を直接消す。 -/
lemma arrowMk_map_comp_eqToHom {D : Type*} [Category D] (F : C ⥤ D)
    {X Y Z : C} (f : X ⟶ Y) (h : Y = Z) :
    Arrow.mk (F.map f ≫ F.map (eqToHom h)) = Arrow.mk (F.map f) := by
  cases h
  simp

/-- 中央の対象の輸送を含む合成で、左の恒等成分を消す。 -/
lemma arrowMk_map_transport_comp_of_left_identity {D : Type*} [Category D] (F : C ⥤ D)
    {A B C' E : C} (f : A ⟶ B) (h : B = C') (g : C' ⟶ E) {W : D}
    (hf : Arrow.mk (F.map f) = Arrow.mk (𝟙 W)) :
    Arrow.mk (F.map (f ≫ eqToHom h ≫ g)) = Arrow.mk (F.map g) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, F.map_comp]
  exact arrowMk_comp_of_left_identity _ _ hf

/-- 中央の対象の輸送を含む合成で、右の恒等成分を消す。 -/
lemma arrowMk_map_transport_comp_of_right_identity {D : Type*} [Category D] (F : C ⥤ D)
    {A B C' E : C} (f : A ⟶ B) (h : B = C') (g : C' ⟶ E) {W : D}
    (hg : Arrow.mk (F.map g) = Arrow.mk (𝟙 W)) :
    Arrow.mk (F.map (f ≫ eqToHom h ≫ g)) = Arrow.mk (F.map f) := by
  cases h
  simp only [eqToHom_refl, Category.id_comp, F.map_comp]
  exact arrowMk_comp_of_right_identity _ _ hg

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
