module
public import SerrePositivity.HomologicalAlgebra.CochainTensorLinear
public import SerrePositivity.PerfectComplex.TensorPerfect
public import SerrePositivity.HomologicalAlgebra.CochainTensorSymmetry
public import SerrePositivity.HomologicalAlgebra.CochainTensorHomotopy

/-! # Tensor products preserve homotopies and scalar null homotopies -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]

/-- Tensoring quasi-isomorphisms between strictly perfect complexes preserves quasi-isomorphisms. -/
lemma cochainTensorMap_quasiIso {P P' Q Q' : CochainComplex (ModuleCat.{u} R) ℤ}
    (hp : strictlyPerfectComplex R P) (hp' : strictlyPerfectComplex R P')
    (hq : strictlyPerfectComplex R Q) (hq' : strictlyPerfectComplex R Q')
    (f : P ⟶ P') (g : Q ⟶ Q') [QuasiIso f] [QuasiIso g] :
    QuasiIso (cochainTensorMap f g) := by
  obtain ⟨e, he⟩ := (strictlyPerfectComplex_quasiIso_iff hp hp' f).mp inferInstance
  obtain ⟨e', he'⟩ := (strictlyPerfectComplex_quasiIso_iff hq hq' g).mp inferInstance
  apply (strictlyPerfectComplex_quasiIso_iff
    (strictlyPerfectComplex_cochainTensor P Q hp hq)
    (strictlyPerfectComplex_cochainTensor P' Q' hp' hq') _).mpr
  exact ⟨cochainTensorHomotopyEquiv e e', by simp [cochainTensorHomotopyEquiv, he, he']⟩
end SerrePositivity
