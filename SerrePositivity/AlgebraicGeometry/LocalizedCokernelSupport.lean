module

public import SerrePositivity.AlgebraicGeometry.FiniteSupportConductor
public import Mathlib.Algebra.Module.LocalizedModule.Submodule

/-!
概要：中心外での局所化の全射性から、余核の台と導手を制御する。
方針：局所化した余核の消滅を台の定義へ戻す。
規約：局所化の射は元の線形写像から誘導される実際の射。
使われ方：有限な変更の中心外の同型から、導手の冪の評価を得る。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u v w
variable {R : Type u} [CommRing R]
variable {M : Type v} {N : Type w} [AddCommGroup M] [Module R M]
variable [AddCommGroup N] [Module R N]

/-- 中心外で局所化した射が全射なら、その余核の台は中心内にある。 -/
theorem cokernel_support_subset_of_localized_surjective (φ : M →ₗ[R] N) (I : Ideal R)
    (h : ∀ P : PrimeSpectrum R, P ∉ PrimeSpectrum.zeroLocus (I : Set R) →
      Function.Surjective (LocalizedModule.map P.asIdeal.primeCompl φ)) :
    Module.support R (N ⧸ φ.range) ⊆ PrimeSpectrum.zeroLocus (I : Set R) := by
  intro P hP
  by_contra hPI
  have hz : Subsingleton (LocalizedModule P.asIdeal.primeCompl (N ⧸ φ.range)) :=
    (LinearMap.localizedMap_surjective_iff_subsingleton_localized_coker _ φ).mp (h P hPI)
  exact (Module.notMem_support_iff.mpr hz) hP

/-- 中心外で局所化した有限環拡大が全射なら、中心の冪の拡大は元の環の像に入る。 -/
theorem finiteLocalizedSurjective_exists_pow_map_lift
    {A : Type u} {B : Type v} [CommRing A] [CommRing B]
    [Algebra A B] [Module.Finite A B] (I : Ideal A) (hI : I.FG)
    (h : ∀ P : PrimeSpectrum A, P ∉ PrimeSpectrum.zeroLocus (I : Set A) →
      Function.Surjective (LocalizedModule.map P.asIdeal.primeCompl (Algebra.linearMap A B))) :
    ∃ n : ℕ, ∀ b ∈ (I ^ n).map (algebraMap A B), ∃ a : A, algebraMap A B a = b := by
  apply finiteSupport_exists_pow_map_lift I hI
  exact cokernel_support_subset_of_localized_surjective (Algebra.linearMap A B) I h

end SerrePositivity.AlgebraicGeometry
