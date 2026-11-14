module
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.Iso
/-!
概要：実切断を持つ span の二つの指定同型から、同じ関手の射作用を回収する。
方針：切断と左脚の合成から指定逆を同定し、右脚の合成を使う。
規約：指定同型を再選択しない。使われ方：一般準同型の span 比較。
-/
@[expose] public section
universe u₁ v₁ u₂ v₂
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory
lemma functor_splitSpan_comparison_hom
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (F : C ⥤ D) {P Q T : C} (s : P ⟶ T) (l : T ⟶ P) (r : T ⟶ Q) (f : P ⟶ Q)
    (hl : s ≫ l = 𝟙 P) (hr : s ≫ r = f)
    (e : F.obj T ≅ F.obj P) (d : F.obj T ≅ F.obj Q)
    (he : e.hom = F.map l) (hd : d.hom = F.map r) :
    e.inv ≫ d.hom = F.map f := by
  have hs : F.map s = e.inv := by
    calc
      F.map s = (F.map s ≫ e.hom) ≫ e.inv := by simp only [Category.assoc,
        Iso.hom_inv_id, Category.comp_id]
      _ = e.inv := by rw [he, ← F.map_comp, hl, F.map_id, Category.id_comp]
  rw [← hs, hd, ← F.map_comp, hr]
end SerrePositivity.InfinityCategories.Project.DerivedCategories
