module

public import SerrePositivity.HomotopicalAlgebra.Replacement.FibrantCategory
public import Mathlib.AlgebraicTopology.ModelCategory.FibrantObjectHomotopy
public import Mathlib.CategoryTheory.Localization.Construction

/-! # Homotopical target functors ignore replacement comparisons over the same base map -/

@[expose] public section
universe v u vH uH vD uD
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.ModelReplacement.FibrantReplacementObject
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {H : Type uH} [Category.{vH} H] (Q : C ⥤ H)
  [Q.IsLocalization (weakEquivalences C)]

lemma localized_map_eq_of_base_eq {X Y : FibrantReplacementObject C} (f g : X ⟶ Y)
    (h : f.base = g.base) : Q.map f.map = Q.map g.map := by
  have : IsIso (Q.map X.inclusion) :=
    Localization.inverts Q (weakEquivalences C) _ X.trivial.2
  apply (cancel_epi (Q.map X.inclusion)).mp
  rw [← Q.map_comp, ← Q.map_comp, f.under, g.under, h]

variable {D : Type uD} [Category.{vD} D] (F : FibrantObject C ⥤ D)
  (hF : (weakEquivalences (FibrantObject C)).IsInvertedBy F)

include Q hF in
/-- The equality is in D itself when F already inverts weak equivalences. -/
lemma homotopical_map_eq_of_base_eq {X Y : FibrantReplacementObject C} (f g : X ⟶ Y)
    (h : f.base = g.base) :
    F.map ((fibrantTargets (C := C)).map f) = F.map ((fibrantTargets (C := C)).map g) := by
  let G := Localization.lift F hF (FibrantObject.ι ⋙ Q)
  let e : (FibrantObject.ι ⋙ Q) ⋙ G ≅ F :=
    Localization.fac F hF (FibrantObject.ι ⋙ Q)
  have hf := e.hom.naturality ((fibrantTargets (C := C)).map f)
  have hg := e.hom.naturality ((fibrantTargets (C := C)).map g)
  apply (cancel_epi (e.hom.app ((fibrantTargets (C := C)).obj X))).mp
  exact hf.symm.trans ((congrArg (fun k => G.map k ≫
    e.hom.app ((fibrantTargets (C := C)).obj Y))
      (localized_map_eq_of_base_eq Q f g h)).trans hg)

end SerrePositivity.ModelReplacement.FibrantReplacementObject
