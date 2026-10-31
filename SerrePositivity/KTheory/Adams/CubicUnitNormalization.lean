module

public import SerrePositivity.KTheory.Adams.TensorCubeUnitRotation
public import SerrePositivity.PerfectComplex.KoszulClasses
public import SerrePositivity.PerfectComplex.Eigen.CubicClass
public import SerrePositivity.KTheory.Adams.CyclicThree

/-! # The cyclic Adams cube preserves the scalar unit class -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity
open CategoryTheory Category Limits TensorProduct
variable {R : Type u} [CommRing R] [Invertible (3 : R)]
namespace Adams

lemma tensorCubeClass_unit_on (E : Type v) [CommRing E]
    (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E)
    (Z : TopologicalSpace.Closeds (PrimeSpectrum R))
    (hs : HasHomologySupportOn Z (oneKoszulUnit (R := R))) :
    tensorCubeClass E t ht ζ (oneKoszulUnit (R := R)) Z oneKoszulUnit_perfect hs =
      (1 : E) ⊗ₜ[ℤ] K0WithSupport.mk Z
        (supportedPerfectOnObj Z oneKoszulUnit oneKoszulUnit_perfect hs) := by
  have he := CochainCubicAction.weightedK0Class_of_map_eq_id E
    (tensorCubeAction (oneKoszulUnit (R := R))) tensorCubeUnit_rotation t ht ζ Z
    (tensorCube_perfect _ oneKoszulUnit_perfect) (tensorCube_support oneKoszulUnit_perfect hs)
  have hm := K0WithSupport.mk_eq_of_quasiIso Z (tensorCube (oneKoszulUnit (R := R)))
    oneKoszulUnit (tensorCube_perfect _ oneKoszulUnit_perfect) oneKoszulUnit_perfect
    (tensorCube_support oneKoszulUnit_perfect hs) hs (tensorCubeUnitIso (R := R)).hom
  exact he.trans (congrArg (fun x => (1 : E) ⊗ₜ[ℤ] x) hm)

lemma tensorCubeClass_unit (E : Type v) [CommRing E]
    (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E) :
    tensorCubeClass E t ht ζ (oneKoszulUnit (R := R)) ⊤
      oneKoszulUnit_perfect oneKoszulUnit_support =
        (1 : E) ⊗ₜ[ℤ] (cyclicUnitClass (R := R)) :=
  tensorCubeClass_unit_on E t ht ζ ⊤ oneKoszulUnit_support

lemma cyclicThree_unit (E : Type v) [CommRing E]
    (t : R) (ht : t ^ 2 + t + 1 = 0) (ζ : E) (hζ : ζ ^ 2 + ζ + 1 = 0) :
    cyclicThree E t ht ζ hζ ⊤ ((1 : E) ⊗ₜ[ℤ] (cyclicUnitClass (R := R))) =
      (1 : E) ⊗ₜ[ℤ] (cyclicUnitClass (R := R)) := by
  rw [cyclicUnitClass, cyclicThree_mk_concrete, one_smul]
  exact tensorCubeClass_unit E t ht ζ

end Adams
end SerrePositivity
