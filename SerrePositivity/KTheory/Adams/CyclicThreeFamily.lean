module

public import SerrePositivity.KTheory.Adams.Family
public import SerrePositivity.KTheory.Adams.CubicKoszulNormalization
public import SerrePositivity.KTheory.Adams.TensorCubeMultiplicativity
public import SerrePositivity.KTheory.Adams.CubicBaseChangeNaturality
public import SerrePositivity.KTheory.Adams.CubicSupportNaturality
public import SerrePositivity.KTheory.Adams.CubicUnitNormalization

/-! # The cyclic Adams cube supplies the common localization-family contract -/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
namespace SerrePositivity
open TensorProduct
variable {R : Type u} [CommRing R]
namespace Adams
variable [Invertible (3 : R)]

def supportedCyclicThree (E : Type v) [CommRing E] (t : R) (ht : t ^ 2 + t + 1 = 0)
    (ζ : E) (hζ : ζ ^ 2 + ζ + 1 = 0) : SupportedAdams R E 3 where
  two_le := by decide
  operation := cyclicThree E t ht ζ hζ
  enlarge := cyclicThree_enlarge E t ht ζ hζ
  cup := cyclicThree_cup E t ht ζ hζ
  unit := cyclicThree_unit E t ht ζ hζ
  koszul_one := cyclicThree_oneKoszul E t ht ζ hζ

lemma cyclicThree_koszul (E : Type v) [CommRing E] (t : R) (ht : t ^ 2 + t + 1 = 0)
    (ζ : E) (hζ : ζ ^ 2 + ζ + 1 = 0) {n : ℕ} (x : Fin n → R) :
    cyclicThree E t ht ζ hζ (koszulClosedSupport x) ((1 : E) ⊗ₜ[ℤ] koszulClass x) =
      (3 : E) ^ n • ((1 : E) ⊗ₜ[ℤ] koszulClass x) :=
  (supportedCyclicThree E t ht ζ hζ).koszul x

/-- A source inverse for 3 supplies one in every algebra over the source. -/
@[instance_reducible]
def algebraInvertibleThree (A : Type u) [CommRing A] [Algebra R A] : Invertible (3 : A) := by
  simpa only [map_ofNat] using Invertible.map (algebraMap R A) (3 : R)

omit [Invertible (3 : R)] in
lemma cubicRelation_map {A : Type u} [CommRing A] (φ : R →+* A)
    (t : R) (ht : t ^ 2 + t + 1 = 0) : (φ t) ^ 2 + φ t + 1 = 0 := by
  simpa only [map_add, map_pow, map_one, map_zero] using congrArg φ ht

/-- The same cubic operation on every localization model, with explicit root transport. -/
def cyclicThreeFamily (E : Type v) [CommRing E] (t : R) (ht : t ^ 2 + t + 1 = 0)
    (ζ : E) (hζ : ζ ^ 2 + ζ + 1 = 0) : LocalizationAdamsFamily R E 3 where
  atBase := supportedCyclicThree E t ht ζ hζ
  atLocalization _ A := by
    intro _ _ _
    let := algebraInvertibleThree (R := R) A
    exact supportedCyclicThree E (algebraMap R A t) (cubicRelation_map (algebraMap R A) t ht) ζ hζ
  base_naturality := by
    intro P A _ _ _ Z W h x
    let := algebraInvertibleThree (R := R) A
    exact cyclicThree_map E (algebraMap R A) t ht (cubicRelation_map (algebraMap R A) t ht)
      ζ hζ Z W h x
  localization_naturality := by
    intro P Q A B _ _ _ _ _ _ φ hφ Z W h x
    let := algebraInvertibleThree (R := R) A
    let := algebraInvertibleThree (R := R) B
    have he : φ (algebraMap R A t) = algebraMap R B t := DFunLike.congr_fun hφ t
    have hn := cyclicThree_map E φ (algebraMap R A t)
      (cubicRelation_map (algebraMap R A) t ht)
      (cubicRelation_map φ (algebraMap R A t) (cubicRelation_map (algebraMap R A) t ht))
      ζ hζ Z W h x
    simpa only [supportedCyclicThree, he] using hn

end Adams
end SerrePositivity
