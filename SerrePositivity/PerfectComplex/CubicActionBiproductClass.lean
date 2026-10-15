module

public import SerrePositivity.PerfectComplex.CubicActionShortExact
public import SerrePositivity.PerfectComplex.BiproductPerfect

/-! # Binary sums of cubic actions and their character classes -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
namespace SerrePositivity
open CategoryTheory Category Limits TensorProduct
variable {R : Type u} [CommRing R]
namespace CochainCubicAction
variable {K L : CochainComplex (ModuleCat.{u} R) ℤ}

variable [Invertible (3 : R)]

lemma eigenK0Class_biprod (τ : CochainCubicAction K) (σ : CochainCubicAction L)
    (t : R) (ht : t ^ 2 + t + 1 = 0)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R)) (j : Fin 3)
    (hp : strictlyPerfectComplex R K) (hq : strictlyPerfectComplex R L)
    (hs : HasHomologySupportOn Z K) (hs' : HasHomologySupportOn Z L) :
    (τ.biprod σ).eigenK0Class t ht Z (strictlyPerfectComplex_biprod hp hq) (hs.biprod hs') j =
      τ.eigenK0Class t ht Z hp hs j + σ.eigenK0Class t ht Z hq hs' j := by
  let S : ShortComplex (CochainComplex (ModuleCat.{u} R) ℤ) :=
    ShortComplex.mk (Limits.biprod.inl : K ⟶ K ⊞ L) Limits.biprod.snd (by simp)
  let spl : S.Splitting := ShortComplex.Splitting.ofHasBinaryBiproduct K L
  exact eigenK0Class_shortExact S τ (τ.biprod σ) σ
    (by simp [S, biprod]) (by simp [S, biprod]) t ht Z j spl.shortExact
    hp (strictlyPerfectComplex_biprod hp hq) hq hs (hs.biprod hs') hs'

lemma weightedK0Class_biprod (E : Type v) [CommRing E]
    (τ : CochainCubicAction K) (σ : CochainCubicAction L)
    (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hp : strictlyPerfectComplex R K) (hq : strictlyPerfectComplex R L)
    (hs : HasHomologySupportOn Z K) (hs' : HasHomologySupportOn Z L) :
    (τ.biprod σ).weightedK0Class E t ht ζ Z (strictlyPerfectComplex_biprod hp hq)
        (hs.biprod hs') =
      τ.weightedK0Class E t ht ζ Z hp hs + σ.weightedK0Class E t ht ζ Z hq hs' := by
  unfold weightedK0Class
  simp_rw [eigenK0Class_biprod τ σ t ht Z _ hp hq hs hs']
  simp only [tmul_add, Finset.sum_add_distrib]

end CochainCubicAction
end SerrePositivity
