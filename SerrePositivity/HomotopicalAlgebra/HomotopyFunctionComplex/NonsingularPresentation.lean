module

public import SerrePositivity.HomotopicalAlgebra.HomotopyFunctionComplex.PresentationLifting
public import Mathlib.AlgebraicTopology.SimplicialSet.Nonsingular
public import Mathlib.AlgebraicTopology.SimplicialSet.NonDegenerateSimplicesColimit
public import Mathlib.AlgebraicTopology.SimplicialSet.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.FiniteLimits

/-! # Presentations of nonsingular simplicial sets by their actual simplices

The nondegenerate-simplex poset gives a canonical diagram in the simplex
category. Its standard-simplex colimit is X. If X is finite, the value of
this diagram on a cosimplicial object needs only finite colimits.
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
  map φ := SSet.N.monoOfLE (leOfHom φ)
  map_id x := SSet.N.monoOfLE_refl x
  map_comp φ ψ := (SSet.N.monoOfLE_comp (leOfHom φ) (leOfHom ψ)).symm

def diagramIso : diagram X ⋙ SSet.stdSimplex.{v} ≅ X.functorN :=
  NatIso.ofComponents (fun x ↦ SSet.Nonsingular.iso x.simplex x.nonDegenerate) (by
    intro x y φ
    apply (cancel_mono y.subcomplex.ι).mp
    change (SSet.stdSimplex.map (SSet.N.monoOfLE (leOfHom φ)) ≫
      (SSet.Nonsingular.iso y.simplex y.nonDegenerate).hom) ≫ y.subcomplex.ι =
        ((SSet.Nonsingular.iso x.simplex x.nonDegenerate).hom ≫
          SSet.Subcomplex.homOfLE (leOfHom φ)) ≫ y.subcomplex.ι
    simp only [Category.assoc, SSet.Nonsingular.iso_hom,
      SSet.Subcomplex.toOfSimplex_ι, SSet.Subcomplex.homOfLE_ι]
    exact SSet.N.stdSimplex_map_monoOfLE_yonedaEquiv_symm_simplex (leOfHom φ))

abbrev cocone : Cocone (diagram X ⋙ SSet.stdSimplex.{v}) :=
  (Cocone.precompose (diagramIso X).hom).obj X.coconeN

def isColimit : IsColimit (cocone X) :=
  (IsColimit.precomposeHomEquiv (diagramIso X) X.coconeN).symm X.isColimitCoconeN

@[simp]
lemma cocone_ι (x : X.N) : (cocone X).ι.app x = SSet.yonedaEquiv.symm x.simplex := by
  change (SSet.Nonsingular.iso x.simplex x.nonDegenerate).hom ≫ x.subcomplex.ι = _
  exact SSet.Subcomplex.toOfSimplex_ι _

@[instance_reducible]
def indexFinCategory [X.Finite] : FinCategory X.N where
  fintypeObj := Fintype.ofFinite _
  fintypeHom _ _ := Fintype.ofFinite _

variable {C : Type u} [Category.{v} C] (A : SimplexCategory ⥤ C)

instance hasColimit [X.Finite] [HasFiniteColimits C] : HasColimit (diagram X ⋙ A) := by
  let := indexFinCategory X
  infer_instance

abbrev homEquiv [HasColimit (diagram X ⋙ A)] (Y : C) :
    (X ⟶ (cosimplicialHom A).obj Y) ≃ (colimit (diagram X ⋙ A) ⟶ Y) :=
  HomPresentation.homEquiv (diagram X) (cocone X) (isColimit X) A

end SerrePositivity.HomotopyFunctionComplex.NonsingularPresentation
