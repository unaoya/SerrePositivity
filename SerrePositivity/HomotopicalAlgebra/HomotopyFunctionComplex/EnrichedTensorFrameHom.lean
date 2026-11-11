module

public import SerrePositivity.CategoryTheory.Enriched.TensorCotensor
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.AdjunctionHom
public import SerrePositivity.HomotopicalAlgebra.Simplicial.UniverseLiftWeakEquivalence

/-! # Hom on a tensor frame is Hom into the enriched mapping object

The actual isomorphism is natural in the C-valued source. Both simplicial
Hom universes are lifted to their common maximum; the original Hom
universes of V and C remain independent.
-/

@[expose] public section
universe vV uV vC uC
noncomputable section
open CategoryTheory HomotopicalAlgebra

namespace SerrePositivity.HomotopyFunctionComplex.EnrichedTensorFrame
variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  {C : Type uC} [Category.{vC} C] [EnrichedOrdinaryCategory V C]
  (P : SerrePositivity.Enriched.TensorCotensor V C)
  (A : SimplexCategory ⥤ V)

abbrev family : C ⥤ (SimplexCategory ⥤ C) :=
  P.tensor.flip ⋙ (Functor.whiskeringLeft SimplexCategory V C).obj A

def homIso (X Y : C) :
    SSet.uliftFunctor.{vV, vC}.obj ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom ((family P A).obj X)).obj Y) ≅
      SSet.uliftFunctor.{vC, vV}.obj ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj (X ⟶[V] Y)) :=
  (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.adjunctionHomIso (P.tensorHom.adj X) A).app Y

lemma homIso_source {X Z : C} (f : X ⟶ Z) (Y : C) :
    SSet.uliftFunctor.{vV, vC}.map
        ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap ((family P A).map f)).app Y) ≫ (homIso P A X Y).hom =
      (homIso P A Z Y).hom ≫ SSet.uliftFunctor.{vC, vV}.map
        ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map (((eHomFunctor V C).map f.op).app Y)) := by
  ext n g
  apply ULift.ext
  exact P.tensorHom.homEquiv_naturality_one f g.down

variable [ModelCategory SSet.{vC}] [ModelCategory SSet.{vV}]
  [ModelCategory SSet.{max vC vV}]
  (hcofC : cofibrations SSet.{vC} = MorphismProperty.monomorphisms _)
  (hfibC : fibrations SSet.{vC} = SSet.modelCategoryQuillen.J.{vC}.rlp)
  (hcofV : cofibrations SSet.{vV} = MorphismProperty.monomorphisms _)
  (hfibV : fibrations SSet.{vV} = SSet.modelCategoryQuillen.J.{vV}.rlp)
  (hcofB : cofibrations SSet.{max vC vV} = MorphismProperty.monomorphisms _)
  (hfibB : fibrations SSet.{max vC vV} = SSet.modelCategoryQuillen.J.{max vC vV}.rlp)

include hcofC hfibC hcofV hfibV hcofB hfibB in
lemma weakEquivalence_iff {X Z : C} (f : X ⟶ Z) (Y : C) :
    weakEquivalences SSet.{vC} ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHomMap ((family P A).map f)).app Y) ↔
      weakEquivalences SSet.{vV}
        ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map (((eHomFunctor V C).map f.op).app Y)) := by
  apply SimplicialModel.UniverseLift.weakEquivalences_iff_of_liftedArrowIso
    hcofC hfibC hcofB hfibB hcofV hfibV
  exact Arrow.isoMk (homIso P A Z Y) (homIso P A X Y) (homIso_source P A f Y).symm

end SerrePositivity.HomotopyFunctionComplex.EnrichedTensorFrame
