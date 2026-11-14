module

public import SerrePositivity.AlgebraicGeometry.FiniteSupportPower
public import Mathlib.RingTheory.Localization.BaseChange

/-!
概要：素点でのテンソル積の消滅から台の包含と中心の冪による零化を得る。
方針：局所化加群と局所化環とのテンソル積の同型を使う。
規約：局所化は各素イデアルの補集合で行う。
使われ方：実際の Čech の flat 底変換による消滅を台の議論へ戻す。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u v
variable {R : Type u} [CommRing R]
variable (M : Type v) [AddCommGroup M] [Module R M]

/-- 中心外の各素点でテンソル積が零なら、加群の台は中心内。 -/
theorem support_subset_of_localizedTensor_subsingleton (I : Ideal R)
    (h : ∀ P : PrimeSpectrum R, P ∉ PrimeSpectrum.zeroLocus (I : Set R) →
      Subsingleton (TensorProduct R (Localization P.asIdeal.primeCompl) M)) :
    Module.support R M ⊆ PrimeSpectrum.zeroLocus (I : Set R) := by
  intro P hP
  by_contra hPI
  letI := h P hPI
  have hz : Subsingleton (LocalizedModule P.asIdeal.primeCompl M) :=
    (LocalizedModule.equivTensorProduct P.asIdeal.primeCompl M).injective.subsingleton
  exact (Module.notMem_support_iff.mpr hz) hP

/-- 有限加群が中心外の局所化テンソル積で消えれば、中心のある冪が加群を消す。 -/
theorem finiteLocalizedTensor_exists_pow_le_annihilator [Module.Finite R M]
    (I : Ideal R) (hI : I.FG)
    (h : ∀ P : PrimeSpectrum R, P ∉ PrimeSpectrum.zeroLocus (I : Set R) →
      Subsingleton (TensorProduct R (Localization P.asIdeal.primeCompl) M)) :
    ∃ n : ℕ, I ^ n ≤ Module.annihilator R M :=
  finiteSupport_exists_pow_le_annihilator M I hI
    (support_subset_of_localizedTensor_subsingleton M I h)

end SerrePositivity.AlgebraicGeometry
