module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.CoconeHomotopyCriterion
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-! 二つの実鎖写像の直和は、それぞれがホモトピー同型なら同じくホモトピー同型。 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory Limits DifferentialGraded
variable (R : Type u) [CommRing R] {P S P' S' : Complex R} (f : P ⟶ P') (g : S ⟶ S')
local notation "Qh" => _root_.HomotopyCategory.quotient (ModuleCat R) (ComplexShape.up ℤ)

/-- 元の両射が K で同型なら、同じ直和鎖写像も K で同型。 -/
lemma dgGluingBiprodHomotopy_isIso (hf : IsIso ((Qh).map f)) (hg : IsIso ((Qh).map g)) :
    IsIso ((Qh).map (biprod.map f g)) := by
  have := hf
  have := hg
  have : PreservesBinaryBiproducts Qh :=
    preservesBinaryBiproducts_of_preservesBiproducts Qh
  have he : (Qh).map (biprod.map f g) =
      ((Qh).mapBiprod P S).hom ≫ biprod.map ((Qh).map f) ((Qh).map g) ≫
        ((Qh).mapBiprod P' S').inv := by
    apply (cancel_mono ((Qh).mapBiprod P' S').hom).1
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    apply biprod.hom_ext <;>
      simp [← CategoryTheory.Functor.map_comp, Category.assoc]
  have : IsIso (biprod.map ((Qh).map f) ((Qh).map g)) := by
    change IsIso (biprod.mapIso (asIso ((Qh).map f)) (asIso ((Qh).map g))).hom
    infer_instance
  rw [he]
  infer_instance

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
