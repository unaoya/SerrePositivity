module
public import SerrePositivity.PerfectComplex.CubicActionBasic
public import SerrePositivity.CategoryTheory.Triangulated.Idempotent

/-! # Transport of cubic chain actions along an isomorphism -/
@[expose] public noncomputable section
namespace SerrePositivity.CochainCubicAction
open CategoryTheory Category
universe u
variable {R : Type u} [CommRing R]
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

def comapIso (e : K ≅ L) (τ : CochainCubicAction L) : CochainCubicAction K where
  map := e.hom ≫ τ.map ≫ e.inv
  cube := conjugate_cube e τ.map τ.cube

@[reassoc]
lemma comapIso_hom (e : K ≅ L) (τ : CochainCubicAction L) :
    (comapIso e τ).map ≫ e.hom = e.hom ≫ τ.map := by
  simp [comapIso, Category.assoc]

end SerrePositivity.CochainCubicAction
