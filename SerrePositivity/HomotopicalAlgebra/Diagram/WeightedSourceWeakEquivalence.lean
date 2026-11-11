module

public import SerrePositivity.HomotopicalAlgebra.Diagram.SmallHomYonedaWeight
public import SerrePositivity.HomotopicalAlgebra.Diagram.WeightedSourceComparison

/-! # The actual weighted source comparison is a weak equivalence

The cofibrant Yoneda weight, its realization and a model-category lift
prove the missing realization step. Source Hom and simplicial universes
remain independent. No projective cofibrancy of the constant unit is used.
-/

@[expose] public section
universe w v u
noncomputable section
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory HomotopicalAlgebra

namespace SerrePositivity.DiagramModel.WeightedSourceComparison
variable (K : Type w) [SmallCategory K] {C : Type u} [Category.{v} C]
  [ModelCategory C] [IsLocallyPresentable.{w} C]
  (I J : MorphismProperty C) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} I J]
  [ModelCategory SSet.{w}]
  (IS JS : MorphismProperty SSet.{w}) [_root_.SerrePositivity.InfinityCategories.HA.ModelCategoryComparison.CofibrantlyGenerated.{w} IS JS]
  (hcof : cofibrations SSet.{w} = MorphismProperty.monomorphisms _)
  (hfib : fibrations SSet.{w} = SSet.modelCategoryQuillen.J.{w}.rlp)

include hcof hfib in
lemma comparison_weakEquivalence (D : K ⥤ C) :
    weakEquivalences C (comparison K I J D (HomotopyCones.weightComparison Kᵒᵖ IS JS)) := by
  apply (comparison_weakEquivalence_iff K I J D _).mpr
  exact SmallHomYonedaWeight.map_weightComparison_weakEquivalence K (frames K I J D)
    I J IS JS hcof hfib
    (fun k => EvaluatedFrame.reedyCofibrant K I J (D, k))
    (fun k => EvaluatedFrame.homotopicallyConstant K I J (D, k))
    (DegreeZeroHomotopyColimit.isCofibrant K I J D)

end SerrePositivity.DiagramModel.WeightedSourceComparison
