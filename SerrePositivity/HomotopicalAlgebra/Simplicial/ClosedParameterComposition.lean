module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.ParameterComposition

/-! # Shared-parameter composition transposes to the standard internal-Hom composition -/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.ClosedParameterComposition
variable {X Y Z T : SSet.{v}}

lemma curry_comp (f : X ⊗ T ⟶ Y) (g : Y ⊗ T ⟶ Z) :
    curry (ParameterComposition.comp f g) =
      lift (curry f) (curry g) ≫ MonoidalClosed.comp X Y Z := by
  apply uncurry_injective
  rw [uncurry_curry, uncurry_natural_left, MonoidalClosed.comp_eq, uncurry_curry,
    MonoidalClosed.compTranspose_eq]
  ext n x
  have hf := types_congr_hom (congr_app (uncurry_curry f) n) x
  rw [uncurry_eq] at hf
  have hg := types_congr_hom (congr_app (uncurry_curry g) n) (f.app n x, x.2)
  rw [uncurry_eq] at hg
  change ((ihom.ev X).app Y).app n (x.1, (curry f).app n x.2) = f.app n x at hf
  change ((ihom.ev Y).app Z).app n (f.app n x, (curry g).app n x.2) =
    g.app n (f.app n x, x.2) at hg
  change g.app n (f.app n x, x.2) = ((ihom.ev Y).app Z).app n
    (((ihom.ev X).app Y).app n (x.1, (curry f).app n x.2), (curry g).app n x.2)
  rw [hf]
  exact hg.symm

lemma curry_fst (X T : SSet.{v}) :
    curry (fst X T) = toUnit T ≫ MonoidalClosed.id X := by
  rw [fst_def, curry_natural_left, MonoidalClosed.id_eq]
  rfl

end SerrePositivity.SimplicialModel.ClosedParameterComposition
