module

public import SerrePositivity.HomotopicalAlgebra.Diagram.ContinuousRelativeCofibrancy
public import SerrePositivity.HomotopicalAlgebra.Diagram.HomotopyColimit

/-! # Actual hocolim comparisons for continuous cofibrant sequences

This first comparison assumes a cofibrant initial object. Removing that
assumption using original left properness is a separate step.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra

namespace SerrePositivity.DiagramModel.HomotopyColimit
variable {K : Type w} [LinearOrder K] [OrderBot K] [SuccOrder K] [WellFoundedLT K]
  {C : Type u} [Category.{v} C] [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]

lemma comparison_weakEquivalence_of_continuous (D : K ⥤ C) [D.IsWellOrderContinuous]
    (hbot : IsCofibrant (D.obj ⊥))
    (hstep : ∀ (k : K), ¬IsMax k → cofibrations C (D.map (homOfLE (Order.le_succ k)))) :
    weakEquivalences C ((comparison K I J).app D) :=
  comparison_weakEquivalence_of_cofibrant K I J D
    (Projective.isCofibrant_of_continuous I J D hbot hstep)

end SerrePositivity.DiagramModel.HomotopyColimit
