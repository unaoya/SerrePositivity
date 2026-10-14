module

public import SerrePositivity.CommutativeAlgebra.CubicCyclotomicClosedPoint
public import Mathlib.RingTheory.Localization.AtPrime.Basic

/-! # Localizing a polynomial quotient at a coprime irreducible factor -/

@[expose] public section
noncomputable section
universe u
namespace SerrePositivity
open Polynomial
variable {K : Type u} [Field K] (g h : K[X]) [Fact (Irreducible g)]

/-- The factor quotient map out of the product quotient. -/
def adjoinRootFactorMap : AdjoinRoot (g * h) →+* AdjoinRoot g :=
  AdjoinRoot.map (RingHom.id K) (g * h) g (by simp)

def adjoinRootFactorIdeal : Ideal (AdjoinRoot (g * h)) :=
  RingHom.ker (adjoinRootFactorMap g h)

instance adjoinRootFactorIdeal_isMaximal : (adjoinRootFactorIdeal g h).IsMaximal :=
  RingHom.ker_isMaximal_of_surjective _
    (adjoinRoot_map_surjective (RingHom.id K) Function.surjective_id _ _ _)

lemma adjoinRootFactorMap_mk (q : K[X]) :
    adjoinRootFactorMap g h (AdjoinRoot.mk (g * h) q) = AdjoinRoot.mk g q := by
  simpa only [adjoinRootFactorMap, Polynomial.map_id] using
    adjoinRoot_map_mk (RingHom.id K) (g * h) g _ q

lemma cofactor_mem_primeCompl (hc : IsCoprime g h) :
    AdjoinRoot.mk (g * h) h ∈ (adjoinRootFactorIdeal g h).primeCompl := by
  have hu := hc.map (AdjoinRoot.mk g)
  rw [AdjoinRoot.mk_self, isCoprime_zero_left] at hu
  change adjoinRootFactorMap g h (AdjoinRoot.mk (g * h) h) ≠ 0
  rw [adjoinRootFactorMap_mk]
  exact hu.ne_zero

variable (T : Type u) [CommRing T] [Algebra (AdjoinRoot (g * h)) T]
    [IsLocalization (adjoinRootFactorIdeal g h).primeCompl T]

/-- The cofactor is inverted at the factor point, so the factor itself vanishes. -/
lemma factor_eq_zero_in_localization (hc : IsCoprime g h) :
    algebraMap (AdjoinRoot (g * h)) T (AdjoinRoot.mk (g * h) g) = 0 := by
  have hu : IsUnit (algebraMap (AdjoinRoot (g * h)) T (AdjoinRoot.mk (g * h) h)) :=
    IsLocalization.map_units T ⟨_, cofactor_mem_primeCompl g h hc⟩
  have hz : algebraMap (AdjoinRoot (g * h)) T (AdjoinRoot.mk (g * h) g) *
      algebraMap (AdjoinRoot (g * h)) T (AdjoinRoot.mk (g * h) h) = 0 := by
    rw [← map_mul, ← map_mul, AdjoinRoot.mk_self, map_zero]
  apply hu.mul_right_cancel
  simpa only [zero_mul] using hz

lemma factorRoot_relation (hc : IsCoprime g h) :
    g.eval₂ ((algebraMap (AdjoinRoot (g * h)) T).comp (AdjoinRoot.of (g * h)))
      (algebraMap (AdjoinRoot (g * h)) T (AdjoinRoot.root (g * h))) = 0 := by
  rw [← hom_eval₂, ← AdjoinRoot.algebraMap_eq, ← aeval_def, AdjoinRoot.aeval_eq]
  exact factor_eq_zero_in_localization g h T hc

/-- The factor quotient maps back to the localization because the factor has become zero. -/
def factorLocalizationInverse (hc : IsCoprime g h) : AdjoinRoot g →+* T :=
  AdjoinRoot.lift ((algebraMap (AdjoinRoot (g * h)) T).comp (AdjoinRoot.of (g * h)))
    (algebraMap (AdjoinRoot (g * h)) T (AdjoinRoot.root (g * h)))
    (factorRoot_relation g h T hc)

lemma factorLocalizationInverse_comp (hc : IsCoprime g h) :
    (factorLocalizationInverse g h T hc).comp (adjoinRootFactorMap g h) =
      algebraMap (AdjoinRoot (g * h)) T := by
  ext r <;> simp [factorLocalizationInverse, adjoinRootFactorMap]

/-- Nonzero images of denominators give the forward localization map to the factor field. -/
def factorLocalizationMap : T →+* AdjoinRoot g :=
  IsLocalization.lift (M := (adjoinRootFactorIdeal g h).primeCompl)
    (fun s => (show adjoinRootFactorMap g h s ≠ 0 from s.property).isUnit)

lemma factorLocalizationMap_comp :
    (factorLocalizationMap g h T).comp (algebraMap (AdjoinRoot (g * h)) T) =
      adjoinRootFactorMap g h := IsLocalization.lift_comp _

lemma factorLocalizationMap_inverse_comp (hc : IsCoprime g h) :
    (factorLocalizationMap g h T).comp (factorLocalizationInverse g h T hc) =
      RingHom.id (AdjoinRoot g) := by
  ext r <;> simp [factorLocalizationInverse, factorLocalizationMap,
    IsLocalization.lift_eq, adjoinRootFactorMap]

/-- The localized product quotient is canonically the irreducible factor field. -/
def coprimeFactorLocalizationEquiv (hc : IsCoprime g h) : T ≃+* AdjoinRoot g := by
  refine RingEquiv.ofRingHom (factorLocalizationMap g h T)
    (factorLocalizationInverse g h T hc) ?_ ?_
  · exact factorLocalizationMap_inverse_comp g h T hc
  · apply IsLocalization.ringHom_ext (adjoinRootFactorIdeal g h).primeCompl
    rw [RingHom.comp_assoc, factorLocalizationMap_comp, factorLocalizationInverse_comp]
    rfl

lemma isField_coprimeFactorLocalization (hc : IsCoprime g h) : IsField T :=
  (coprimeFactorLocalizationEquiv g h T hc).toMulEquiv.isField
    (inferInstance : Field (AdjoinRoot g)).toIsField

end SerrePositivity
