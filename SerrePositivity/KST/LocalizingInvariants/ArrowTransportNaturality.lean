module

public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Quasicategory.ArrowTransportNaturality
public import SerrePositivity.KST.LocalizingInvariants.FunctorHomArrowTransport

/-!
概要：端点込みの Arrow の等号を、指定した等号同型との可換式へ戻す。
方針：始点・終点の等号を消去し、固定端点の射の等号を回収する。
規約：任意の同型に置き換えない。使われ方：BF 模型の頂点表示と整数 π の輸送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u v w z
open CategoryTheory
namespace SerrePositivity.KST.LocalizingInvariants

lemma arrow_eqToHom_naturality {C : Type u} [Category.{v} C] {a b a' b' : C}
    (f : a ⟶ b) (g : a' ⟶ b') (ha : a = a') (hb : b = b')
    (h : Arrow.mk f = Arrow.mk g) : f ≫ eqToHom hb = eqToHom ha ≫ g := by
  subst a' b'
  rw [hom_eq_of_arrow_mk_eq h]
  simp only [eqToHom_refl, Category.comp_id, Category.id_comp]

lemma arrow_eqToHom_map_naturality {C : Type u} [Category.{v} C]
    {D : Type w} [Category.{z} D] (F : C ⥤ D) {a b a' b' : C}
    (f : a ⟶ b) (g : F.obj a' ⟶ F.obj b') (ha : a = a') (hb : b = b')
    (h : Arrow.mk (F.map f) = Arrow.mk g) :
    F.map f ≫ F.map (eqToHom hb) = F.map (eqToHom ha) ≫ g := by
  subst a' b'
  simp only [eqToHom_refl]
  rw [F.map_id, F.map_id, Category.comp_id, Category.id_comp]
  exact hom_eq_of_arrow_mk_eq h

end SerrePositivity.KST.LocalizingInvariants
