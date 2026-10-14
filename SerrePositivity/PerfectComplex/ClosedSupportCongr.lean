module
public import SerrePositivity.PerfectComplex.ClosedSupportK0

/-! # Changing equal closed supports -/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity
variable {R : Type u} [CommRing R]

/-- Change equal closed supports. -/
def supportedPerfectOnCongr {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (h : Z = W) (X : SupportedPerfectHomotopyOn Z) : SupportedPerfectHomotopyOn W := by
  subst W
  exact X

lemma supportedPerfectOnCongr_obj {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)}
    (h : Z = W) (X : SupportedPerfectHomotopyOn Z) :
    (supportedPerfectOnCongr h X).obj.obj = X.obj.obj := by
  subst W
  rfl

namespace K0WithSupport
/-- The additive equivalence obtained by changing equal supports. -/
def congr {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Z = W) :
    K0WithSupport Z ≃+ K0WithSupport W := by
  subst W
  exact AddEquiv.refl _

lemma congr_mk {Z W : TopologicalSpace.Closeds (PrimeSpectrum R)} (h : Z = W)
    (X : SupportedPerfectHomotopyOn Z) : congr h (mk _ X) = mk _ (supportedPerfectOnCongr h X) := by
  subst W
  rfl

end K0WithSupport
end SerrePositivity
