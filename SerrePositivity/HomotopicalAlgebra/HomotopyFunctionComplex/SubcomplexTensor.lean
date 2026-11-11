module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.NonsingularPresentation
public import Mathlib.AlgebraicTopology.SimplicialSet.Horn
public import Mathlib.AlgebraicTopology.SimplicialSet.Boundary

/-! # Tensor maps for subcomplexes of a standard simplex

The source of the tensor map is the finite colimit of actual values of A
over nondegenerate simplices of the subcomplex. Its lifting property
transports to the actual subcomplex inclusion, including horns and boundaries.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.HomotopyFunctionComplex.SubcomplexTensor
variable {n : SimplexCategory} (S : (SSet.stdSimplex.{v}.obj n).Subcomplex)

abbrev diagram := NonsingularPresentation.diagram S.toSSet

abbrev simplexMap (x : S.toSSet.N) : SimplexCategory.mk x.dim ⟶ n :=
  SSet.stdSimplex.fullyFaithful.preimage (SSet.yonedaEquiv.symm x.simplex ≫ S.ι)

def simplexCocone : Cocone (diagram S) where
  pt := n
  ι :=
    { app x := simplexMap S x
      naturality x y φ := by
        change SSet.N.monoOfLE (leOfHom φ) ≫ simplexMap S y = simplexMap S x ≫ 𝟙 n
        rw [Category.comp_id]
        apply SSet.stdSimplex.fullyFaithful.map_injective
        rw [SSet.stdSimplex.map_comp, Functor.FullyFaithful.map_preimage,
          Functor.FullyFaithful.map_preimage, ← Category.assoc,
          SSet.N.stdSimplex_map_monoOfLE_yonedaEquiv_symm_simplex] }

lemma presentationMap_eq :
    HomPresentation.presentationMap (diagram S) (NonsingularPresentation.cocone S.toSSet)
      (NonsingularPresentation.isColimit S.toSSet) (simplexCocone S) = S.ι := by
  apply (NonsingularPresentation.isColimit S.toSSet).hom_ext
  intro x
  change (NonsingularPresentation.cocone S.toSSet).ι.app x ≫
      HomPresentation.presentationMap (diagram S) (NonsingularPresentation.cocone S.toSSet)
        (NonsingularPresentation.isColimit S.toSSet) (simplexCocone S) =
    (NonsingularPresentation.cocone S.toSSet).ι.app x ≫ S.ι
  exact ((NonsingularPresentation.isColimit S.toSSet).fac
    (SSet.stdSimplex.mapCocone (simplexCocone S)) x).trans
      (SSet.stdSimplex.fullyFaithful.map_preimage _)

variable {C : Type u} [Category.{v} C] (A : SimplexCategory ⥤ C)
  [HasFiniteColimits C]

abbrev obj := colimit (diagram S ⋙ A)

abbrev inclusion : obj S A ⟶ A.obj n :=
  HomPresentation.tensorMap (diagram S) A (simplexCocone S)

abbrev homEquiv (Y : C) : (S.toSSet ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y) ≃ (obj S A ⟶ Y) :=
  NonsingularPresentation.homEquiv S.toSSet A Y

lemma hasLiftingProperty {Y Z : C} (p : Y ⟶ Z) [HasLiftingProperty (inclusion S A) p] :
    HasLiftingProperty S.ι ((_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).map p) := by
  have : HasLiftingProperty (HomPresentation.tensorMap (diagram S) A (simplexCocone S)) p :=
    inferInstanceAs (HasLiftingProperty (inclusion S A) p)
  have h := HomPresentation.hasLiftingProperty (diagram S)
    (NonsingularPresentation.cocone S.toSSet) (NonsingularPresentation.isColimit S.toSSet)
    A (simplexCocone S) p
  rwa [presentationMap_eq S] at h

end SerrePositivity.HomotopyFunctionComplex.SubcomplexTensor
