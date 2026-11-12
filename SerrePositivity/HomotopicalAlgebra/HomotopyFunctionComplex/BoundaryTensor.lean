module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.BoundaryIndex
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.CofibrantBoundary
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.Reedy.SimplexFinite
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.TensorKanCriterion

/-! # Boundary tensors are the actual Reedy latching maps

The comparison uses the constructed equivalence of index categories and
an arrow isomorphism. Hence the boundary tensor condition is proved from
Reedy cofibrancy, rather than postulated as another frame hypothesis.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [HasFiniteColimits C]
  (A : SimplexCategory ⥤ C) (n : ℕ)

abbrev boundaryTensorIso : SubcomplexTensor.obj (SSet.boundary.{v} n) A ≅
    (latchingEvaluation simplex (SimplexCategory.mk n)).obj A :=
  HasColimit.isoOfEquivalence
    (F := SubcomplexTensor.diagram (SSet.boundary.{v} n) ⋙ A)
    (G := latchingSource simplex (SimplexCategory.mk n) ⋙ A)
    (BoundaryIndex.equivalence.{v} n)
    (Iso.refl (SubcomplexTensor.diagram (SSet.boundary.{v} n) ⋙ A))

@[reassoc (attr := simp)]
lemma ι_boundaryTensorIso_hom (x : (BoundaryIndex.X.{v} n).N) :
    colimit.ι (SubcomplexTensor.diagram (SSet.boundary.{v} n) ⋙ A) x ≫
      (boundaryTensorIso A n).hom =
        colimit.ι (latchingSource simplex (SimplexCategory.mk n) ⋙ A)
          ((BoundaryIndex.toLatching.{v} n).obj x) := by
  have h := HasColimit.ι_isoOfEquivalence_hom
      (F := SubcomplexTensor.diagram (SSet.boundary.{v} n) ⋙ A)
      (G := latchingSource simplex (SimplexCategory.mk n) ⋙ A)
      (BoundaryIndex.equivalence.{v} n)
      (Iso.refl (SubcomplexTensor.diagram (SSet.boundary.{v} n) ⋙ A)) x
  exact h.trans (Category.id_comp
    (colimit.ι (latchingSource simplex (SimplexCategory.mk n) ⋙ A)
      ((BoundaryIndex.toLatching.{v} n).obj x)))

lemma boundaryTensorIso_comparison :
    SubcomplexTensor.inclusion (SSet.boundary.{v} n) A =
      (boundaryTensorIso A n).hom ≫ (latchingComparison simplex (SimplexCategory.mk n)).app A := by
  apply colimit.hom_ext
  intro x
  change colimit.ι (SubcomplexTensor.diagram (SSet.boundary.{v} n) ⋙ A) x ≫
      colimit.desc _ (A.mapCocone (SubcomplexTensor.simplexCocone (SSet.boundary.{v} n))) =
    colimit.ι (SubcomplexTensor.diagram (SSet.boundary.{v} n) ⋙ A) x ≫
      ((boundaryTensorIso A n).hom ≫
        colimit.desc _ (latchingCocone simplex A (SimplexCategory.mk n)))
  have hL : colimit.ι (SubcomplexTensor.diagram (SSet.boundary.{v} n) ⋙ A) x ≫
      colimit.desc _ (A.mapCocone (SubcomplexTensor.simplexCocone (SSet.boundary.{v} n))) =
        A.map (SubcomplexTensor.simplexMap (SSet.boundary.{v} n) x) :=
    colimit.ι_desc _ _
  have hR : colimit.ι (latchingSource simplex (SimplexCategory.mk n) ⋙ A)
      ((BoundaryIndex.toLatching.{v} n).obj x) ≫
        colimit.desc _ (latchingCocone simplex A (SimplexCategory.mk n)) =
          A.map (SubcomplexTensor.simplexMap (SSet.boundary.{v} n) x) :=
    colimit.ι_desc _ _
  have h := congrArg
    (fun f ↦ f ≫ colimit.desc _ (latchingCocone simplex A (SimplexCategory.mk n)))
      (ι_boundaryTensorIso_hom A n x)
  exact hL.trans ((h.trans hR).symm.trans (Category.assoc _ _ _))

def boundaryTensorArrowIso : Arrow.mk (SubcomplexTensor.inclusion (SSet.boundary.{v} n) A) ≅
    Arrow.mk ((latchingComparison simplex (SimplexCategory.mk n)).app A) :=
  Arrow.isoMk (boundaryTensorIso A n) (Iso.refl _) (by
    exact (boundaryTensorIso_comparison A n).symm.trans
      (Category.comp_id (SubcomplexTensor.inclusion (SSet.boundary.{v} n) A)).symm)

lemma boundaryTensor_cofibration [ModelCategory C]
    (hA : reedyLeft simplex (cofibrations C) (initial.to A)) :
    cofibrations C (SubcomplexTensor.inclusion (SSet.boundary.{v} n) A) :=
  ((cofibrations C).arrow_iso_iff (boundaryTensorArrowIso A n)).mpr
    (latchingComparison_cofibration simplex (SimplexCategory.mk n) A (hA _))

lemma boundary_lifting_of_reedyCofibrant [ModelCategory C]
    (hA : reedyLeft simplex (cofibrations C) (initial.to A))
    {Y Z : C} (p : Y ⟶ Z) [Fibration p] [WeakEquivalence p] :
    HasLiftingProperty (SSet.boundary.{v} n).ι ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map p) :=
  boundary_lifting_of_cofibration A (fun m ↦ boundaryTensor_cofibration A m hA) p n

end SerrePositivity.HomotopyFunctionComplex
