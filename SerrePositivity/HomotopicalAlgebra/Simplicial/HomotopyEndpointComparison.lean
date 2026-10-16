module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.LargeParameterRelativeChoice

/-! # Compare actual selected homotopies relative to both entire endpoint families

Only finite fillers in the small value space are used. Both original
homotopies remain literal parameter faces of the comparison.
-/

@[expose] public section
universe r w v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.HomotopyEndpointComparison

lemma face_zero {K Q : SSet.{r}} {e₀ e₁ : K ⟶ Q} (H : SSet.Homotopy e₀ e₁) :
    K ◁ SSet.stdSimplex.δ (1 : Fin 2) ≫ H.h = fst K _ ≫ e₀ := by
  have h : K ◁ SSet.stdSimplex.δ (1 : Fin 2) = fst K _ ≫ SSet.ι₀ := by
    rw [SSet.stdSimplex.δ_one_eq_const]
    rfl
  rw [h, Category.assoc, H.h₀]

lemma face_one {K Q : SSet.{r}} {e₀ e₁ : K ⟶ Q} (H : SSet.Homotopy e₀ e₁) :
    K ◁ SSet.stdSimplex.δ (0 : Fin 2) ≫ H.h = fst K _ ≫ e₁ := by
  have h : K ◁ SSet.stdSimplex.δ (0 : Fin 2) = fst K _ ≫ SSet.ι₁ := by
    rw [SSet.stdSimplex.δ_zero_eq_const]
    rfl
  rw [h, Category.assoc, H.h₁]

lemma boundary_eq {K Q : SSet.{r}} {e₀ e₁ : K ⟶ Q} (H : SSet.Homotopy e₀ e₁) :
    K ◁ (SSet.boundary.{r} 1).ι ≫ H.h = LargeParameterHomotopy.boundaryMap e₀ e₁ := by
  apply (LargeParameterHomotopy.boundaryColimit K).hom_ext
  rintro ⟨i⟩
  cases i with
  | left =>
    change (K ◁ SSet.boundary.ι (1 : Fin 2)) ≫ _ =
      (K ◁ SSet.boundary.ι (1 : Fin 2)) ≫ LargeParameterHomotopy.boundaryMap e₀ e₁
    rw [← Category.assoc, ← whiskerLeft_comp, SSet.boundary.ι_ι,
      face_zero, LargeParameterHomotopy.boundaryMap_zero]
  | right =>
    change (K ◁ SSet.boundary.ι (0 : Fin 2)) ≫ _ =
      (K ◁ SSet.boundary.ι (0 : Fin 2)) ≫ LargeParameterHomotopy.boundaryMap e₀ e₁
    rw [← Category.assoc, ← whiskerLeft_comp, SSet.boundary.ι_ι,
      face_one, LargeParameterHomotopy.boundaryMap_one]

variable {P : SSet.{v}} (hp : UniverseLift.BoundaryFillers P) {K : SSet.{max w v}}
  {e₀ e₁ : K ⟶ UniverseLift.obj.{w} P} (H H' : SSet.Homotopy e₀ e₁)

/-- Both actual homotopies are retained and both original endpoint families stay fixed. -/
abbrev homotopy : SSet.Homotopy H.h H'.h :=
  LargeParameterRelativeChoice.homotopy hp (K ◁ (SSet.boundary.{max w v} 1).ι)
    (LargeParameterHomotopy.boundaryMap e₀ e₁) H.h H'.h (boundary_eq H) (boundary_eq H')

lemma fixed_endpoints : (K ◁ (SSet.boundary.{max w v} 1).ι) ▷
    SSet.stdSimplex.{max w v}.obj (SimplexCategory.mk 1) ≫ (homotopy hp H H').h =
      (K ⊗ (SSet.boundary.{max w v} 1).toSSet) ◁
          (SSet.stdSimplex.isTerminalObj₀.from _ ≫ RelativeChoiceSpace.pointUnitIso.hom) ≫
        (ρ_ _).hom ≫ LargeParameterHomotopy.boundaryMap e₀ e₁ :=
  LargeParameterRelativeChoice.homotopy_relative _ _ _ _ _ _ _

end SerrePositivity.SimplicialModel.HomotopyEndpointComparison
