module

public import Mathlib.CategoryTheory.Adjunction.Limits
public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.FiniteTensorBoundary
public import SerrePositivity.HomotopicalAlgebra.Quillen.Adjunction

/-! # Reedy cofibrancy of standard simplices under a left Quillen functor

Finite nonsingular presentations are actual colimits of standard simplices.
A left adjoint preserves these presentations, identifying their constructed
finite tensor with its own value. Boundary inclusions then prove Reedy
cofibrancy, without a separate assumed latching condition.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open SerrePositivity.Reedy SerrePositivity.Quillen

namespace SerrePositivity.HomotopyFunctionComplex.StandardCosimplicial
variable {C : Type u} [Category.{v} C] [HasFiniteColimits C]
  (F : SSet.{v} ⥤ C) [F.IsLeftAdjoint]

abbrev diagram : SimplexCategory ⥤ C := SSet.stdSimplex ⋙ F

variable (K : SSet.{v}) [K.Nonsingular] [K.Finite]

abbrev tensorCocone : Cocone (NonsingularPresentation.diagram K ⋙ diagram F) :=
  F.mapCocone (NonsingularPresentation.cocone K)

def tensorCoconeIsColimit : IsColimit (tensorCocone F K) :=
  isColimitOfPreserves F (NonsingularPresentation.isColimit K)

abbrev tensorIso : FiniteTensor.obj (diagram F) K ≅ F.obj K :=
  (colimit.isColimit _).coconePointUniqueUpToIso (tensorCoconeIsColimit F K)

@[reassoc]
lemma ι_tensorIso_hom (x : K.N) :
    colimit.ι (NonsingularPresentation.diagram K ⋙ diagram F) x ≫ (tensorIso F K).hom =
      F.map ((NonsingularPresentation.cocone K).ι.app x) :=
  (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom (tensorCoconeIsColimit F K) x

lemma tensorIso_inclusion {n : SimplexCategory} (S : (SSet.stdSimplex.{v}.obj n).Subcomplex) :
    (tensorIso F S.toSSet).hom ≫ F.map S.ι = SubcomplexTensor.inclusion S (diagram F) := by
  apply colimit.hom_ext
  intro x
  have hi := ι_tensorIso_hom F S.toSSet x
  have hs : SSet.stdSimplex.map (SubcomplexTensor.simplexMap S x) =
      (NonsingularPresentation.cocone S.toSSet).ι.app x ≫ S.ι :=
    SSet.stdSimplex.fullyFaithful.map_preimage _
  have hd : colimit.ι (SubcomplexTensor.diagram S ⋙ diagram F) x ≫
      SubcomplexTensor.inclusion S (diagram F) = F.map (SSet.stdSimplex.map
        (SubcomplexTensor.simplexMap S x)) := colimit.ι_desc _ _
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun f ↦ f ≫ F.map S.ι) hi).trans
      ((F.map_comp _ _).symm.trans ((congrArg F.map hs.symm).trans hd.symm)))

end SerrePositivity.HomotopyFunctionComplex.StandardCosimplicial
