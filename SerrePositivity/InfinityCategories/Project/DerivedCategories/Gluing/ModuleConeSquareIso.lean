module
public import SerrePositivity.DifferentialGraded.Module.Hom.ConeComparison

/-! 実加群同型の可換正方形に沿う cone 同型と、両方向の包含の厳密な比較。 -/
@[expose] public section
open CategoryTheory SerrePositivity.DifferentialGraded
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
variable (R : Type u) [CommRing R] (C : Type v) [DGCategory R C] [Small.{u} C]
  {P Q S T : ModuleCategory R C} (f : P ⟶ Q) (g : S ⟶ T)
  (e : P ≅ S) (e' : Q ≅ T) (comm : f ≫ e'.hom = e.hom ≫ g)
include comm in
lemma dgGluingModuleConeSquareIso_inverse_square : g ≫ e'.inv = e.inv ≫ f := by
  calc
    g ≫ e'.inv = e.inv ≫ (e.hom ≫ g) ≫ e'.inv := by
      simp only [← Category.assoc, e.inv_hom_id, Category.id_comp]
    _ = e.inv ≫ (f ≫ e'.hom) ≫ e'.inv := by rw [← comm]
    _ = e.inv ≫ f := by simp only [Category.assoc, e'.hom_inv_id, Category.comp_id]

def dgGluingModuleConeSquareIso : moduleCone R C f ≅ moduleCone R C g where
  hom := moduleConeMap R C f g e.hom e'.hom comm
  inv := moduleConeMap R C g f e.inv e'.inv
    (dgGluingModuleConeSquareIso_inverse_square R C f g e e' comm)
  hom_inv_id := by
    rw [← moduleConeMap_comp]
    simpa only [Iso.hom_inv_id] using moduleConeMap_id R C f
  inv_hom_id := by
    rw [← moduleConeMap_comp]
    simpa only [Iso.inv_hom_id] using moduleConeMap_id R C g

lemma dgGluingModuleConeSquareIso_inr :
    moduleConeInr R C f ≫ (dgGluingModuleConeSquareIso R C f g e e' comm).hom =
      e'.hom ≫ moduleConeInr R C g := moduleConeMap_inr R C f g e.hom e'.hom comm

lemma dgGluingModuleConeSquareIso_inv_inr :
    moduleConeInr R C g ≫ (dgGluingModuleConeSquareIso R C f g e e' comm).inv =
      e'.inv ≫ moduleConeInr R C f :=
  moduleConeMap_inr R C g f e.inv e'.inv
    (dgGluingModuleConeSquareIso_inverse_square R C f g e e' comm)

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
