module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.RelativeChoiceSpace
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-! # Gluing cotensor families on the actual two-vertex interval boundary -/

@[expose] public section
universe v
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed

namespace SerrePositivity.SimplicialModel.BoundaryOneCotensor
abbrev vertex := SSet.stdSimplex.{v}.obj (SimplexCategory.mk 0)
abbrev boundary := (SSet.boundary.{v} 1).toSSet
abbrev zero : vertex.{v} ⟶ boundary.{v} := SSet.boundary.ι (1 : Fin 2)
abbrev one : vertex.{v} ⟶ boundary.{v} := SSet.boundary.ι (0 : Fin 2)

/-- Tensoring the actual boundary coproduct retains its universal property. -/
def tensorIsColimit (T : SSet.{v}) : IsColimit (BinaryCofan.mk (zero ▷ T) (one ▷ T)) := by
  exact mapIsColimitOfPreservesOfIsColimit (tensorRight T) _ _
    HomotopyFunctionComplex.BoundaryOne.isColimit

variable {T P : SSet.{v}} (a b : T ⟶ (ihom vertex).obj P)

def glue : T ⟶ (ihom boundary).obj P :=
  curry ((tensorIsColimit T).desc (BinaryCofan.mk (uncurry a) (uncurry b)))

@[reassoc]
lemma glue_zero : glue a b ≫ (pre zero).app P = a := by
  apply uncurry_injective
  rw [uncurry_pre_app, glue, uncurry_curry]
  exact (tensorIsColimit T).fac (BinaryCofan.mk (uncurry a) (uncurry b)) ⟨WalkingPair.left⟩

@[reassoc]
lemma glue_one : glue a b ≫ (pre one).app P = b := by
  apply uncurry_injective
  rw [uncurry_pre_app, glue, uncurry_curry]
  exact (tensorIsColimit T).fac (BinaryCofan.mk (uncurry a) (uncurry b)) ⟨WalkingPair.right⟩

lemma hom_ext {f g : T ⟶ (ihom boundary).obj P}
    (h₀ : f ≫ (pre zero).app P =
      g ≫ (pre zero).app P)
    (h₁ : f ≫ (pre one).app P =
      g ≫ (pre one).app P) : f = g := by
  apply uncurry_injective
  apply (tensorIsColimit T).hom_ext
  intro j
  rcases j with ⟨j⟩
  cases j
  · exact (uncurry_pre_app _ f zero).symm.trans
      ((congrArg uncurry h₀).trans (uncurry_pre_app _ g zero))
  · exact (uncurry_pre_app _ f one).symm.trans
      ((congrArg uncurry h₁).trans (uncurry_pre_app _ g one))

end SerrePositivity.SimplicialModel.BoundaryOneCotensor
