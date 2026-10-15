module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.TensorFunctor
public import Mathlib.CategoryTheory.HomCongr

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

def representationMap : obj S A ⟶ A.obj k :=
  homEquiv S A (A.obj k)
    (e.inv ≫ (SSet.yonedaEquiv (X := (cosimplicialHom A).obj (A.obj k))).symm (𝟙 _))

lemma representationMap_comp {Y : C} (f : A.obj k ⟶ Y) :
    representationMap A S e ≫ f = homEquiv S A Y
      (e.inv ≫ (SSet.yonedaEquiv (X := (cosimplicialHom A).obj Y)).symm f) := by
  have h : (SSet.yonedaEquiv (X := (cosimplicialHom A).obj (A.obj k))).symm (𝟙 _) ≫
      (cosimplicialHom A).map f =
        (SSet.yonedaEquiv (X := (cosimplicialHom A).obj Y)).symm f :=
    (SSet.yonedaEquiv_symm_comp (𝟙 (A.obj k)) ((cosimplicialHom A).map f)).trans
      (congrArg (SSet.yonedaEquiv (X := (cosimplicialHom A).obj Y)).symm
        (Category.id_comp f))
  exact (homEquiv_naturality A S _ f).symm.trans
    (congrArg (homEquiv S A Y) ((Category.assoc _ _ _).trans
      (congrArg (fun g ↦ e.inv ≫ g) h)))

instance representationMap_isIso : IsIso (representationMap A S e) := by
  apply isIso_of_coyoneda_map_bijective
  intro Y
  let E : (A.obj k ⟶ Y) ≃ (obj S A ⟶ Y) :=
    (SSet.yonedaEquiv (X := (cosimplicialHom A).obj Y)).symm.trans
      ((Iso.homCongr e (Iso.refl _)).trans (homEquiv S A Y))
  have he : (fun f : A.obj k ⟶ Y ↦ representationMap A S e ≫ f) = E := by
    funext f
    simpa only [E, Equiv.trans_apply, Iso.homCongr_apply, Iso.refl_hom, Category.comp_id] using
      representationMap_comp A S e f
  exact he.symm ▸ E.bijective

abbrev representationIso : obj S A ≅ A.obj k := asIso (representationMap A S e)

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
