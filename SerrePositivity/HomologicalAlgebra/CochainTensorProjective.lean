module
public import SerrePositivity.HomologicalAlgebra.CochainTensor
public import SerrePositivity.HomologicalAlgebra.FiniteSupportCoproduct
public import Mathlib.Algebra.Module.Projective

/-! # Degreewise projectivity of the total cochain tensor product -/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits MonoidalCategory
variable {R : Type u} [CommRing R]

/-- Projectivity of the factors implies projectivity of every total tensor degree. -/
lemma cochainTensor_projective_X (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : ∀ i, Module.Projective R (P.X i)) (hq : ∀ j, Module.Projective R (Q.X j)) (n : ℤ) :
    Module.Projective R ((cochainTensor P Q).X n) := by
  have hs : ∀ ij, Projective (cochainTensorSummand P Q n ij) := by
    intro ij
    have := hp ij.val.1
    have := hq ij.val.2
    have ht : Module.Projective R (TensorProduct R (P.X ij.val.1) (Q.X ij.val.2)) :=
      inferInstance
    exact ModuleCat.projective_of_categoryTheory_projective _
  have : Projective ((cochainTensor P Q).X n) :=
    Projective.of_iso (cochainTensorXIso P Q n).symm
      (projective_coproduct_of_projective _ hs)
  infer_instance

end SerrePositivity
