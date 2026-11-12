module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.PresentationLifting
public import Mathlib.AlgebraicTopology.SimplicialSet.NonsingularColimit
public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits
public import Mathlib.CategoryTheory.Whiskering

/-! # Presentations of nonsingular simplicial sets by their actual simplices

Mathlib supplies the canonical nondegenerate-simplex diagram and its
standard-simplex colimit. This interface adds the finite index structure
and the Hom equivalence requiring only finite colimits in C.
-/

@[expose] public section
universe v u
noncomputable section
open CategoryTheory CategoryTheory.Limits
open scoped Simplicial

namespace SerrePositivity.HomotopyFunctionComplex.NonsingularPresentation
variable (X : SSet.{v}) [X.Nonsingular]

def diagram : X.N ⥤ SimplexCategory where
  obj x := SimplexCategory.mk x.dim
  map f := SSet.N.monoOfLE (leOfHom f)
  map_id x := SSet.N.monoOfLE_refl x
  map_comp f g := (SSet.N.monoOfLE_comp (leOfHom f) (leOfHom g)).symm

def mathlibDiagramIso : diagram X ≅
    SSet.N.toSemiSimplexCategory X ⋙ SemiSimplexCategory.toSimplexCategory :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro x y f
    have hm : Mono (SSet.N.monoOfLE (X := X) (leOfHom f)) := inferInstance
    have he := @SemiSimplexCategory.toSimplexCategory_map_homOfMono
      (SemiSimplexCategory.mk x.dim) (SemiSimplexCategory.mk y.dim)
      (SSet.N.monoOfLE (leOfHom f)) hm
    exact (Category.comp_id ((diagram X).map f)).trans
      (he.symm.trans (Category.id_comp
        ((SSet.N.toSemiSimplexCategory X ⋙ SemiSimplexCategory.toSimplexCategory).map f)).symm))

abbrev diagramIso : diagram X ⋙ SSet.stdSimplex.{v} ≅ X.functorN :=
  Functor.isoWhiskerRight (mathlibDiagramIso X) SSet.stdSimplex ≪≫ X.functorN'Iso

abbrev cocone : Cocone (diagram X ⋙ SSet.stdSimplex.{v}) where
  pt := X
  ι.app x := SSet.yonedaEquiv.symm x.simplex
  ι.naturality _ _ f := SSet.N.stdSimplex_map_monoOfLE_yonedaEquiv_symm_simplex (leOfHom f)

def isColimit : IsColimit (cocone X) :=
  (IsColimit.equivOfNatIsoOfIso (Functor.isoWhiskerRight (mathlibDiagramIso X) SSet.stdSimplex).symm
    X.coconeN' (cocone X) (Cocone.ext (Iso.refl _) (by
      intro j
      change (SSet.stdSimplex.map (𝟙 (SimplexCategory.mk j.dim)) ≫
        SSet.yonedaEquiv.symm j.simplex) ≫ 𝟙 X = SSet.yonedaEquiv.symm j.simplex
      have hid := CategoryTheory.Functor.map_id SSet.stdSimplex.{v} (SimplexCategory.mk j.dim)
      have h := (congrArg
        (fun f ↦ f ≫ (SSet.yonedaEquiv (X := X)).symm j.simplex) hid).trans
          (Category.id_comp ((SSet.yonedaEquiv (X := X)).symm j.simplex))
      exact (congrArg (fun f ↦ f ≫ 𝟙 X) h).trans (Category.comp_id _)))).1 X.isColimitCoconeN'

@[simp]
lemma cocone_ι (x : X.N) : (cocone X).ι.app x = SSet.yonedaEquiv.symm x.simplex := rfl

@[instance_reducible]
def indexFinCategory [X.Finite] : FinCategory X.N where
  fintypeObj := Fintype.ofFinite _
  fintypeHom _ _ := Fintype.ofFinite _

variable {C : Type u} [Category.{v} C] (A : SimplexCategory ⥤ C)

instance hasColimit [X.Finite] [HasFiniteColimits C] : HasColimit (diagram X ⋙ A) := by
  let := indexFinCategory X
  infer_instance

abbrev homEquiv [HasColimit (diagram X ⋙ A)] (Y : C) :
    (X ⟶ (_root_.SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.CosimplicialHom.cosimplicialHom A).obj Y) ≃ (colimit (diagram X ⋙ A) ⟶ Y) :=
  HomPresentation.homEquiv (diagram X) (cocone X) (isColimit X) A

end SerrePositivity.HomotopyFunctionComplex.NonsingularPresentation
