module
public import SerrePositivity.PerfectComplex.TensorBaseChange
public import SerrePositivity.HomologicalAlgebra.CochainTensorSingle
public import SerrePositivity.HomologicalAlgebra.StupidTruncation
public import SerrePositivity.HomologicalAlgebra.CochainTensorAcyclic

/-! # Tensoring acyclic complexes with bounded flat complexes -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
namespace SerrePositivity
open CategoryTheory Category Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]

lemma cochainAcyclic_iff_support_bot (P : CochainComplex (ModuleCat.{u} R) ℤ) :
    P.Acyclic ↔ HasHomologySupportOn (⊥ : TopologicalSpace.Closeds (PrimeSpectrum R)) P := by
  rw [hasHomologySupportOn_bot_iff]
  exact forall_congr' (fun i => HomologicalComplex.exactAt_iff_isZero_homology P i)

/-- A strictly perfect right factor preserves arbitrary quasi-isomorphisms. -/
lemma cochainTensor_quasiIso_left_of_perfect
    {P P' : CochainComplex (ModuleCat.{u} R) ℤ}
    (Q : CochainComplex (ModuleCat.{u} R) ℤ) (hq : strictlyPerfectComplex R Q)
    (f : P ⟶ P') [QuasiIso f] : QuasiIso (cochainTensorMap f (𝟙 Q)) := by
  obtain ⟨a, b, ha, hb⟩ := hq.1
  apply cochainTensor_quasiIso_left_of_boundedFlat Q a b
    (fun i hi => Q.isZero_of_isStrictlyGE a i hi)
    (fun i hi => Q.isZero_of_isStrictlyLE b i hi)
  intro i
  have := (hq.2 i).2
  infer_instance
end SerrePositivity
