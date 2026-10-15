module

public import SerrePositivity.PerfectComplex.CubicActionClass
public import SerrePositivity.PerfectComplex.IdempotentImageQuasiIso
public import SerrePositivity.HomologicalAlgebra.CochainIdempotentAcyclic

/-! # Invariance and acyclic vanishing of weighted cubic classes -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity
open CategoryTheory Category Limits TensorProduct
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace CochainCubicAction
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

lemma eigenK0Class_eq_of_quasiIso (τ : CochainCubicAction K) (σ : CochainCubicAction L)
    (f : K ⟶ L) [QuasiIso f] (hf : τ.map ≫ f = f ≫ σ.map)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hpK : strictlyPerfectComplex R K) (hpL : strictlyPerfectComplex R L)
    (hsK : HasHomologySupportOn Z K) (hsL : HasHomologySupportOn Z L) (j : Fin 3) :
    τ.eigenK0Class t ht Z hpK hsK j = σ.eigenK0Class t ht Z hpL hsL j := by
  let e := τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) j
  let d := σ.characterProjector t (cube_eq_one_of_cubic_relation t ht) j
  let he := τ.projectorMap_naturality σ f hf (cubicCharacter t j)
  have : QuasiIso (e.imageMap d f he) := e.imageMap_quasiIso d f he
  exact K0WithSupport.mk_eq_of_quasiIso Z e.image d.image
    (e.image_strictlyPerfect hpK) (d.image_strictlyPerfect hpL)
    (e.image_support hsK) (d.image_support hsL) (e.imageMap d f he)

lemma weightedK0Class_eq_of_quasiIso (E : Type v) [CommRing E]
    (τ : CochainCubicAction K) (σ : CochainCubicAction L)
    (f : K ⟶ L) [QuasiIso f] (hf : τ.map ≫ f = f ≫ σ.map)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E) (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hpK : strictlyPerfectComplex R K) (hpL : strictlyPerfectComplex R L)
    (hsK : HasHomologySupportOn Z K) (hsL : HasHomologySupportOn Z L) :
    τ.weightedK0Class E t ht ζ Z hpK hsK = σ.weightedK0Class E t ht ζ Z hpL hsL := by
  unfold weightedK0Class
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun x => cubicCharacter ζ j ⊗ₜ[ℤ] x)
    (eigenK0Class_eq_of_quasiIso τ σ f hf t ht Z hpK hpL hsK hsL j)

lemma eigenK0Class_eq_zero_of_acyclic (τ : CochainCubicAction K)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K)
    (hac : K.Acyclic) (j : Fin 3) : τ.eigenK0Class t ht Z hp hs j = 0 := by
  let e := τ.characterProjector t (cube_eq_one_of_cubic_relation t ht) j
  exact K0WithSupport.mk_eq_zero_of_acyclic Z
    (e.image_strictlyPerfect hp) (e.image_support hs) (e.image_acyclic hac)

lemma weightedK0Class_eq_zero_of_acyclic (E : Type v) [CommRing E]
    (τ : CochainCubicAction K) (t : R) (ht : t ^ 2 + t + 1 = 0)
    (ζ : E) (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hs : HasHomologySupportOn Z K) (hac : K.Acyclic) :
    τ.weightedK0Class E t ht ζ Z hp hs = 0 := by
  unfold weightedK0Class
  simp only [eigenK0Class_eq_zero_of_acyclic τ t ht Z hp hs hac,
    TensorProduct.tmul_zero, Finset.sum_const_zero]

end CochainCubicAction
end SerrePositivity
