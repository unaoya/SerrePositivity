module

public import SerrePositivity.HomotopicalAlgebra.Simplicial.BarConstruction
public import Mathlib.CategoryTheory.CodiscreteCategory
public import Mathlib.Logic.Small.Basic
public import Mathlib.AlgebraicTopology.SimplicialSet.StdSimplex

/-! # Raw bar size can grow even for a diagram of points

The objects of the indexing category inject into degree zero. Consequently
objectwise small input values alone cannot justify shrinking a raw bar.
-/

@[expose] public section
universe v uD vD
noncomputable section
open CategoryTheory

namespace SerrePositivity.SimplicialModel.BarConstruction
variable (D : Type uD) [Category.{vD} D]

abbrev pointDiagram : D ⥤ SSet.{v} :=
  (Functor.const D).obj (SSet.stdSimplex.obj (SimplexCategory.mk 0))

/-- Distinct index objects remain distinct vertices of the raw bar of a point diagram. -/
def indexVertex (d : D) :
    ((functor D).obj (pointDiagram.{v} D)).obj (Opposite.op (SimplexCategory.mk 0)) :=
  ComposableArrows.mk₀ (((pointDiagram.{v} D).flip.obj
    (Opposite.op (SimplexCategory.mk 0))).elementsMk d (SSet.stdSimplex.obj₀Equiv.symm 0))

lemma indexVertex_injective : Function.Injective (indexVertex.{v} D) := by
  intro x y h
  exact congrArg (fun c => (c.obj 0).obj) h

lemma index_small_of_bar_zero_small
    [Small.{v} (((functor D).obj (pointDiagram.{v} D)).obj
      (Opposite.op (SimplexCategory.mk 0)))] : Small.{v} D :=
  small_of_injective (indexVertex_injective.{v} D)

/-- No model structure or weak-equivalence assertion is involved in the size obstruction. -/
lemma point_bar_not_small :
    ¬ Small.{v} (((functor (Codiscrete (Type v))).obj
      (pointDiagram.{v} (Codiscrete (Type v)))).obj (Opposite.op (SimplexCategory.mk 0))) := by
  intro h
  have := h
  have : Small.{v} (Codiscrete (Type v)) :=
    index_small_of_bar_zero_small.{v} (Codiscrete (Type v))
  apply not_small_type.{v, 0}
  exact small_of_injective (f := fun A : Type v => Codiscrete.mk A)
    (fun _ _ h => congrArg Codiscrete.as h)

end SerrePositivity.SimplicialModel.BarConstruction
