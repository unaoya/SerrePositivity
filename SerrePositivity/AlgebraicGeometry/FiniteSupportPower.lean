module

public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.Finiteness.Ideal

/-!
概要：有限加群の台の閉集合への包含から、イデアルの冪による零化を得る。
方針：台を零化イデアルの零点集合で表し、有限生成イデアルの根基の判定を使う。
規約：基底の Noether 性の代わりに中心の有限生成性を明示できる。
使われ方：有限射の導手の評価と射影 Čech H の台の評価。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u v
variable {R : Type u} [CommRing R] (M : Type v) [AddCommGroup M] [Module R M]
variable [Module.Finite R M]

/-- 有限加群の台が有限生成イデアルの零点集合に入れば、その冪が加群を消す。 -/
theorem finiteSupport_exists_pow_le_annihilator (I : Ideal R) (hI : I.FG)
    (h : Module.support R M ⊆ PrimeSpectrum.zeroLocus (I : Set R)) :
    ∃ n : ℕ, I ^ n ≤ Module.annihilator R M := by
  rw [Module.support_eq_zeroLocus] at h
  exact Ideal.exists_pow_le_of_le_radical_of_fg
    ((PrimeSpectrum.zeroLocus_subset_zeroLocus_iff _ _).mp h) hI

/-- 商加群の台が中心に入ると、元の加群の中心の冪倍は部分加群に入る。 -/
theorem finiteQuotientSupport_exists_pow_smul_mem (N : Submodule R M)
    (I : Ideal R) (hI : I.FG)
    (h : Module.support R (M ⧸ N) ⊆ PrimeSpectrum.zeroLocus (I : Set R)) :
    ∃ n : ℕ, ∀ a ∈ I ^ n, ∀ m : M, a • m ∈ N := by
  obtain ⟨n, hn⟩ := finiteSupport_exists_pow_le_annihilator (M ⧸ N) I hI h
  refine ⟨n, fun a ha m ↦ ?_⟩
  have hz := Module.mem_annihilator.mp (hn ha) (Submodule.Quotient.mk m : M ⧸ N)
  apply (Submodule.Quotient.mk_eq_zero N).mp
  exact hz

end SerrePositivity.AlgebraicGeometry
