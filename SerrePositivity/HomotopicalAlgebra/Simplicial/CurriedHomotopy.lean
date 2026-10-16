module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.LargeParameterSquare

/-! # A specified mapping-space edge gives the same actual interval homotopy -/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.MonoidalCategory CategoryTheory.MonoidalClosed
open CategoryTheory.CartesianMonoidalCategory

namespace SerrePositivity.SimplicialModel.CurriedHomotopy
variable {X K : SSet.{v}} {f g : X ⟶ K}

def ofEdge (e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ (ihom X).obj K)
    (h₀ : SSet.stdSimplex.δ (1 : Fin 2) ≫ e = LargeParameterSquare.point f)
    (h₁ : SSet.stdSimplex.δ (0 : Fin 2) ≫ e = LargeParameterSquare.point g) :
    SSet.Homotopy f g where
  h := uncurry e
  h₀ := by
    change SSet.ι₀ ≫ uncurry e = f
    rw [← LargeParameterHomotopy.section_zero X, Category.assoc,
      ← uncurry_natural_left, h₀, LargeParameterSquare.point, uncurry_curry]
    rfl
  h₁ := by
    change SSet.ι₁ ≫ uncurry e = g
    rw [← LargeParameterHomotopy.section_one X, Category.assoc,
      ← uncurry_natural_left, h₁, LargeParameterSquare.point, uncurry_curry]
    rfl
  rel := by
    apply NatTrans.ext
    funext n
    exact ConcreteCategory.hom_ext _ _ (fun x => False.elim x.1.property)

lemma ofEdge_h (e : SSet.stdSimplex.{v}.obj (SimplexCategory.mk 1) ⟶ (ihom X).obj K)
    (h₀ : SSet.stdSimplex.δ (1 : Fin 2) ≫ e = LargeParameterSquare.point f)
    (h₁ : SSet.stdSimplex.δ (0 : Fin 2) ≫ e = LargeParameterSquare.point g) :
    (ofEdge e h₀ h₁).h = uncurry e := rfl

end SerrePositivity.SimplicialModel.CurriedHomotopy
