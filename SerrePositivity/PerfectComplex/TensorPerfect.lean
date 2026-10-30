module
public import SerrePositivity.HomologicalAlgebra.CochainTensorProjective
public import SerrePositivity.PerfectComplex.ClosedSupportRelations
public import SerrePositivity.HomologicalAlgebra.CochainTensor
public import SerrePositivity.HomologicalAlgebra.CochainTensorFinite

/-! # Bounded finite projective tensor complexes -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits MonoidalCategory
variable {R : Type u} [CommRing R]

/-- The tensor product of strictly perfect complexes is strictly perfect. -/
lemma strictlyPerfectComplex_cochainTensor (P Q : CochainComplex (ModuleCat.{u} R) ℤ)
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q) :
    strictlyPerfectComplex R (cochainTensor P Q) := by
  obtain ⟨a, b, ha, hb⟩ := hp.1
  obtain ⟨c, d, hc, hd⟩ := hq.1
  have hP : ∀ i, i < a ∨ b < i → IsZero (P.X i) := fun i hi => hi.elim
    (fun h => P.isZero_of_isStrictlyGE a i h) (fun h => P.isZero_of_isStrictlyLE b i h)
  refine ⟨⟨a + c, b + d, ?_, ?_⟩, fun n => ?_⟩
  · exact cochainTensor_isStrictlyGE P Q a c
  · exact cochainTensor_isStrictlyLE P Q b d
  · exact ⟨cochainTensor_finite_X P Q (fun i => (hp.2 i).1) (fun j => (hq.2 j).1) a b hP n,
      cochainTensor_projective_X P Q (fun i => (hp.2 i).2) (fun j => (hq.2 j).2) n⟩
end SerrePositivity
