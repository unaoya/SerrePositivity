module

public import SerrePositivity.KTheory.Adams.TensorSquare
public import SerrePositivity.HomologicalAlgebra.CochainTensor.BaseChange

/-! # Compatibility of tensor base change with the signed symmetry -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
open Functor.OplaxMonoidal
variable {R S : Type u} [CommRing R] [CommRing S]

namespace Adams

/-- Base change of the tensor square intertwines its signed involution. -/
@[reassoc]
lemma tensorSquareBaseChangeIso_swap (φ : R →+* S)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    ((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).map
        (tensorSquareSwap P) ≫ (cochainTensorBaseChangeIso φ P P).hom =
      (cochainTensorBaseChangeIso φ P P).hom ≫ tensorSquareSwap (baseChange φ P) :=
  cochainTensorBaseChangeIso_symmetry φ P P

end Adams

end SerrePositivity
