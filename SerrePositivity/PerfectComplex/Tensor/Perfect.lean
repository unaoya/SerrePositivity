module

public import SerrePositivity.HomologicalAlgebra.CochainTensor.Basic
public import SerrePositivity.PerfectComplex.ClosedSupport.Functoriality
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Symmetric
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Bounds

/-! # 完全複体のテンソル積

## 概要

有界な有限射影複体のテンソル積が同じ種類の複体であること、テンソル積が擬同型を保つこと、完全複体のテンソル積のホモロジーの台を与える。

## 方針

テンソル積の各次数は有限個の項の直和で、有限射影性はそこから従う。

## 規約

テンソル積は HomologicalAlgebra/CochainTensor のもの。

## 使われ方

`ClosedSupport/Cup`、`Tensor/CyclicSum`、`Eigen/*`。
-/

@[expose] public noncomputable section

universe u

section TensorPerfectPart

set_option backward.isDefEq.respectTransparency false
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

end TensorPerfectPart

section TensorHomotopyPart

set_option backward.isDefEq.respectTransparency false
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

end TensorHomotopyPart

section TensorSupportPart

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open CategoryTheory Limits MonoidalCategory HomologicalComplex
variable {R : Type u} [CommRing R]

/-- A scalar null homotopy on the first factor gives one on the tensor complex. -/
def cochainTensorScalarNullHomotopy {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (r : R) (h : Homotopy (r • 𝟙 P) 0) : Homotopy (r • 𝟙 (cochainTensor P Q)) 0 := by
  have H := cochainTensorHomotopyLeft h (𝟙 Q)
  simpa only [cochainTensorMap_smul_left, cochainTensorMap_id, cochainTensorMap_zero_left] using H

/-- A bounded perfect factor controls the homology support of its tensor with any complex. -/
lemma HasHomologySupportOn.cochainTensor_left
    {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    {P : CochainComplex (ModuleCat.{u} R) ℤ}
    (hP : HasHomologySupportOn Z P) (hp : strictlyPerfectComplex R P)
    (Q : CochainComplex (ModuleCat.{u} R) ℤ) : HasHomologySupportOn Z (cochainTensor P Q) := by
  obtain ⟨J, hJ⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal _).mp Z.isClosed
  have hZ : Z = supportZeroLocus J := by
    apply TopologicalSpace.Closeds.ext
    exact hJ
  obtain ⟨a, b, ha, hb⟩ := hp.1
  have hbound : ∃ a b : ℤ, ∀ i, i < a ∨ b < i → IsZero (P.X i) :=
    ⟨a, b, fun i hi => hi.elim (fun h => P.isZero_of_isStrictlyGE a i h)
      (fun h => P.isZero_of_isStrictlyLE b i h)⟩
  have hproj : ∀ i, Projective (P.X i) := fun i => by
    have := (hp.2 i).2
    infer_instance
  intro i p hpi
  rw [hZ]
  change J ≤ p.asIdeal
  intro r hr
  have hrP : ∀ i, Module.support R (P.homology i) ⊆ PrimeSpectrum.zeroLocus {r} := by
    intro k
    exact (hP k).trans (by
      rw [hZ]
      exact PrimeSpectrum.zeroLocus_anti_mono (Set.singleton_subset_iff.mpr hr))
  obtain ⟨v, ⟨H⟩⟩ := exists_pow_nullHomotopy_of_homology_support P r
    (fun k => (hp.2 k).1) hproj hbound hrP
  have HT := cochainTensorScalarNullHomotopy (Q := Q) (r ^ v) H
  have h := HT.homologyMap_eq i
  rw [homologyMap_smul, homologyMap_id, homologyMap_zero] at h
  have hv : r ^ v ∈ Module.annihilator R ((cochainTensor P Q).homology i) := by
    rw [Module.mem_annihilator]
    intro x
    exact congrArg (fun f : (cochainTensor P Q).homology i ⟶ _ => f.hom x) h
  exact p.isPrime.mem_of_pow_mem v (Module.annihilator_le_of_mem_support hpi hv)

/-- The support statement for the right factor follows from the signed symmetry. -/
lemma HasHomologySupportOn.cochainTensor_right
    {Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    {Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (hQ : HasHomologySupportOn Z Q) (hq : strictlyPerfectComplex R Q)
    (P : CochainComplex (ModuleCat.{u} R) ℤ) : HasHomologySupportOn Z (cochainTensor P Q) :=
  (hQ.cochainTensor_left hq P).of_iso (cochainTensorSymmetry Q P)

/-- Tensor homology is supported in the intersection of the two factor supports. -/
lemma HasHomologySupportOn.cochainTensor
    {Y Z : TopologicalSpace.Closeds (PrimeSpectrum R)}
    {P Q : CochainComplex (ModuleCat.{u} R) ℤ}
    (hP : HasHomologySupportOn Y P) (hQ : HasHomologySupportOn Z Q)
    (hp : strictlyPerfectComplex R P) (hq : strictlyPerfectComplex R Q) :
    HasHomologySupportOn (Y ⊓ Z) (cochainTensor P Q) :=
  (hasHomologySupportOn_inf _ _ _).mpr
    ⟨hP.cochainTensor_left hp Q, hQ.cochainTensor_right hq P⟩
end SerrePositivity

end TensorSupportPart
