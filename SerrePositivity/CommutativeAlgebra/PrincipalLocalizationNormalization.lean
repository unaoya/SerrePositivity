module

public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Basic

/-! # The original scalar map for a principal open inside R[1/g]

A second localization at f is the localization of R at g times the chosen numerator
of f. The native scalar structure is already the composite of the original maps.
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
variable {R : Type u} [CommRing R]

/-- The native R-algebra map is the composite of the original two localization maps. -/
theorem principalLocalizationTower_algebraMap (g : R) (f : Localization.Away g) (x : R) :
    algebraMap R (Localization.Away f) x =
      algebraMap (Localization.Away g) (Localization.Away f)
        (algebraMap R (Localization.Away g) x) := rfl

/-- The native scalar action retains the original intermediate localization. -/
theorem principalLocalizationTower_scalarTower (g : R) (f : Localization.Away g) :
    IsScalarTower R (Localization.Away g) (Localization.Away f) := inferInstance

/-- A principal open of R[1/g] is the original principal open at g times its numerator. -/
theorem principalLocalizationTower_isLocalization (g : R) (f : Localization.Away g) :
    IsLocalization (.powers (g * (IsLocalization.Away.sec g f).1))
      (Localization.Away f) := by
  apply IsLocalization.Away.mul_of_associated (R := R) (S := Localization.Away g)
    (T := Localization.Away f) (x := g) (z := (IsLocalization.Away.sec g f).1) (y := f)
  have he : algebraMap R (Localization.Away g) (IsLocalization.Away.sec g f).1 =
      (algebraMap R (Localization.Away g) g) ^ (IsLocalization.Away.sec g f).2 * f := by
    rw [← IsLocalization.Away.sec_spec g f, map_pow, mul_comm]
  rw [he]
  exact associated_unit_mul_left f _
    ((IsLocalization.Away.algebraMap_isUnit (S := Localization.Away g) g).pow _)

/-- The normalization is an R-algebra equivalence for the original composite map. -/
def principalLocalizationTowerEquiv (g : R) (f : Localization.Away g) :
    Localization.Away (g * (IsLocalization.Away.sec g f).1) ≃ₐ[R] Localization.Away f := by
  letI := principalLocalizationTower_isLocalization g f
  exact IsLocalization.algEquiv (.powers (g * (IsLocalization.Away.sec g f).1)) _ _

end SerrePositivity
