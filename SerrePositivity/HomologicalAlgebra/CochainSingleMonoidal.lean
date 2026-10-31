module
public import SerrePositivity.HomologicalAlgebra.CochainSingleTensorComparison
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Shuffle

/-! # The actual degree-zero cochain embedding as a symmetric monoidal functor -/
@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory MonoidalCategory
variable {R : Type u} [CommRing R]

/-- Use the actual discrete tensor comparison, including its verified coherence diagrams. -/
def cochainSingleCoreMonoidal :
    (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).CoreMonoidal where
  εIso := Iso.refl _
  μIso := cochainSingleTensorIso
  μIso_hom_natural_left f N := cochainSingleTensorIso_naturality_left f N
  μIso_hom_natural_right M g := cochainSingleTensorIso_naturality_right M g
  associativity M N P := cochainSingleTensorIso_associator M N P
  left_unitality M := by
    simp only [Iso.refl_hom, id_whiskerRight, Category.id_comp]
    exact (cochainSingleTensorIso_leftUnitor M).symm
  right_unitality M := by
    simp only [Iso.refl_hom, whiskerLeft_id, Category.id_comp]
    exact (cochainSingleTensorIso_rightUnitor M).symm

/-- The degree-zero embedding is strong monoidal for the actual cochain tensor. -/
instance cochainSingleFunctorMonoidal :
    (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).Monoidal :=
  (cochainSingleCoreMonoidal (R := R)).toMonoidal

/-- This monoidal embedding also preserves the actual signed symmetry. -/
instance cochainSingleFunctorBraided :
    (CochainComplex.singleFunctor (ModuleCat.{u} R) 0).Braided where
  toMonoidal := cochainSingleFunctorMonoidal (R := R)
  braided M N := (cochainSingleTensorIso_symmetry M N).symm

end SerrePositivity
