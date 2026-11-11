module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.TensorFunctor
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensorRepresentable

/-! # Tensors of representable and empty subcomplexes

A subcomplex represented by a standard simplex has tensor isomorphic to
the corresponding actual value of A. The tensor of the empty subcomplex
is initial. These identifications use the constructed Hom equivalence.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits

namespace SerrePositivity.HomotopyFunctionComplex.SubcomplexTensor
variable {n k : SimplexCategory} {C : Type u} [Category.{v} C] [HasFiniteColimits C]
  (A : SimplexCategory ⥤ C) (S : (SSet.stdSimplex.{v}.obj n).Subcomplex)
  (e : SSet.stdSimplex.{v}.obj k ≅ S.toSSet)

abbrev representationMap : obj S A ⟶ A.obj k :=
  FiniteTensor.representationMap A S.toSSet e

lemma representationMap_comp {Y : C} (f : A.obj k ⟶ Y) :
    representationMap A S e ≫ f = homEquiv S A Y
      (e.inv ≫ (SSet.yonedaEquiv (X := (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y)).symm f) :=
  FiniteTensor.representationMap_comp A S.toSSet e f

instance representationMap_isIso : IsIso (representationMap A S e) :=
  FiniteTensor.representationMap_isIso A S.toSSet e

abbrev representationIso : obj S A ≅ A.obj k := FiniteTensor.representationIso A S.toSSet e

lemma top_representationMap :
    representationMap A (⊤ : (SSet.stdSimplex.{v}.obj n).Subcomplex)
      (SSet.Subcomplex.topIso _).symm =
        inclusion (⊤ : (SSet.stdSimplex.{v}.obj n).Subcomplex) A := by
  have h := HomPresentation.homEquiv_presentationMap
    (diagram (⊤ : (SSet.stdSimplex.{v}.obj n).Subcomplex))
    (NonsingularPresentation.cocone (⊤ : (SSet.stdSimplex.{v}.obj n).Subcomplex).toSSet)
    (NonsingularPresentation.isColimit (⊤ : (SSet.stdSimplex.{v}.obj n).Subcomplex).toSSet)
    A (simplexCocone (⊤ : (SSet.stdSimplex.{v}.obj n).Subcomplex)) (𝟙 (A.obj n))
  rw [presentationMap_eq] at h
  exact h.trans (Category.comp_id _)

instance top_inclusion_isIso :
    IsIso (inclusion (⊤ : (SSet.stdSimplex.{v}.obj n).Subcomplex) A) := by
  rw [← top_representationMap A]
  infer_instance

def isInitialBot : IsInitial (obj (⊥ : (SSet.stdSimplex.{v}.obj n).Subcomplex) A) :=
  IsInitial.ofUniqueHom
    (fun Y ↦ homEquiv (⊥ : (SSet.stdSimplex.{v}.obj n).Subcomplex) A Y
      (SSet.Subcomplex.isInitialBot.to _)) (by
        intro Y m
        apply (homEquiv (⊥ : (SSet.stdSimplex.{v}.obj n).Subcomplex) A Y).symm.injective
        exact SSet.Subcomplex.isInitialBot.hom_ext _ _)

end SerrePositivity.HomotopyFunctionComplex.SubcomplexTensor
