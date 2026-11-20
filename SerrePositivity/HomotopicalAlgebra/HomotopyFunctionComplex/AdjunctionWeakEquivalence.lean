module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.AdjunctionHom
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftWeakEquivalence

/-! # Adjunction transports weak-equivalence tests on actual cosimplicial Hom

The ordinary adjunction isomorphism is compared after lifting both Hom
universes to their common maximum. No model or Quillen structure on the
source and target categories is required for this transport.
-/

@[expose] public section
universe vC uC vD uD
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex
variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
  [ModelCategory SSet.{vC}] [ModelCategory SSet.{vD}] [ModelCategory SSet.{max vC vD}]
  (hcofC : cofibrations SSet.{vC} = MorphismProperty.monomorphisms _)
  (hfibC : fibrations SSet.{vC} = SSet.modelCategoryQuillen.J.{vC}.rlp)
  (hcofD : cofibrations SSet.{vD} = MorphismProperty.monomorphisms _)
  (hfibD : fibrations SSet.{vD} = SSet.modelCategoryQuillen.J.{vD}.rlp)
  (hcofB : cofibrations SSet.{max vC vD} = MorphismProperty.monomorphisms _)
  (hfibB : fibrations SSet.{max vC vD} = SSet.modelCategoryQuillen.J.{max vC vD}.rlp)

include adj hcofC hfibC hcofD hfibD hcofB hfibB in
lemma adjunction_cosimplicialHomMap_weakEquivalence_iff
    {A B : SimplexCategory ⥤ C} (a : A ⟶ B) (Y : D) :
    weakEquivalences SSet.{vD} ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap (Functor.whiskerRight a L)).app Y) ↔
      weakEquivalences SSet.{vC} ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap a).app (R.obj Y)) := by
  apply SimplicialModel.UniverseLift.weakEquivalences_iff_of_liftedArrowIso
    hcofD hfibD hcofB hfibB hcofC hfibC
  exact Arrow.isoMk ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.adjunctionHomIso adj B).app Y) ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.adjunctionHomIso adj A).app Y)
    (congr_app (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.adjunctionHomIso_source_naturality adj a) Y).symm

end SerrePositivity.HomotopyFunctionComplex
