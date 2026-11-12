module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensorRepresentable
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.TensorFunctor
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.BoundaryTensor

/-! # Boundary generators under the finite tensor functor

The action of the general finite tensor functor on an actual boundary
inclusion is isomorphic to the constructed latching map. In particular,
Reedy cofibrancy proves cofibrancy of the images of all boundary generators.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy

namespace SerrePositivity.HomotopyFunctionComplex
variable {C : Type u} [Category.{v} C] [HasFiniteColimits C] (A : SimplexCategory ⥤ C)
  {n : SimplexCategory} (S : (SSet.stdSimplex.{v}.obj n).Subcomplex)

lemma finiteTensor_map_ι : FiniteTensor.map A S.ι ≫
    FiniteTensor.representationMap A (SSet.stdSimplex.obj n) (Iso.refl _) =
      SubcomplexTensor.inclusion S A := by
  have h := FiniteTensor.map_comp_homEquiv_apply A S.ι
    (𝟙 (SSet.stdSimplex.obj n) ≫
      (SSet.yonedaEquiv (X := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj (A.obj n))).symm (𝟙 (A.obj n)))
  have ht := congrArg (SubcomplexTensor.homEquiv S A (A.obj n))
    (congrArg (fun f ↦ S.ι ≫ f)
      (Category.id_comp
        ((SSet.yonedaEquiv (X := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj (A.obj n))).symm (𝟙 _))))
  exact h.trans (ht.trans ((SubcomplexTensor.homEquiv_simplex A S (𝟙 _)).trans
    (Category.comp_id _)))

def finiteTensorInclusionArrowIso : Arrow.mk (FiniteTensor.map A S.ι) ≅
    Arrow.mk (SubcomplexTensor.inclusion S A) :=
  Arrow.isoMk (Iso.refl _) (FiniteTensor.representationIso A (SSet.stdSimplex.obj n) (Iso.refl _))
    (by exact (Category.id_comp _).trans (finiteTensor_map_ι A S).symm)

lemma finiteTensor_boundary_cofibration [ModelCategory C]
    (hA : reedyLeft simplex (cofibrations C) (initial.to A)) (n : ℕ) :
    cofibrations C (FiniteTensor.map A (SSet.boundary.{v} n).ι) :=
  ((cofibrations C).arrow_iso_iff (finiteTensorInclusionArrowIso A _)).mpr
    (boundaryTensor_cofibration A n hA)

end SerrePositivity.HomotopyFunctionComplex
