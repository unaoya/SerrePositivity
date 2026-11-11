module
public import Mathlib.CategoryTheory.NatIso
/-!
概要：指定済みの cell 比較を保って h Fun 値の作用と一般の cell 模型比較を構成する。
方針：同じ比較の共役による関手性と、augmentation の可換四角形の自然性を使う。
規約：原 kernel の平坦性は不要。使われ方：一般 cell 模型の単位・合成・比較の整合性。
-/
@[expose] public section
noncomputable section
universe u v w z
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory
def functorOfObjectIsomorphisms {C : Type u} [Category.{v} C]
    {D : Type w} [Category.{z} D] (F : C ⥤ D) (G : C → D)
    (e : ∀ X, F.obj X ≅ G X) : C ⥤ D where
  obj := G
  map {X Y} f := (e X).inv ≫ F.map f ≫ (e Y).hom
  map_id X := by
    rw [F.map_id]
    simp only [Category.id_comp, Iso.inv_hom_id]
  map_comp {X Y Z} f g := by
    rw [F.map_comp]
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
def functorOfObjectIsomorphismsIso {C : Type u} [Category.{v} C]
    {D : Type w} [Category.{z} D] (F : C ⥤ D) (G : C → D)
    (e : ∀ X, F.obj X ≅ G X) : F ≅ functorOfObjectIsomorphisms F G e :=
  NatIso.ofComponents e (by
    intro X Y f
    simp only [functorOfObjectIsomorphisms, Iso.hom_inv_id_assoc])
lemma functorOfObjectIsomorphisms_map_eq_of_square
    {C : Type u} [Category.{v} C] {D : Type w} [Category.{z} D]
    (F : C ⥤ D) (G : C → D) (e : ∀ X, F.obj X ≅ G X)
    {X Y : C} (f : X ⟶ Y) (b : G X ⟶ G Y)
    (h : (e X).hom ≫ b = F.map f ≫ (e Y).hom) :
    (functorOfObjectIsomorphisms F G e).map f = b := by
  exact (Iso.inv_comp_eq (e X)).2 h.symm
end SerrePositivity.InfinityCategories.Project.DerivedCategories
