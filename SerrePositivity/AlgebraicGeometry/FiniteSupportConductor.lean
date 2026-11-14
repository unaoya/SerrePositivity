module

public import SerrePositivity.AlgebraicGeometry.FiniteSupportPower
public import SerrePositivity.CommutativeAlgebra.UniversalHomeomorphism.PowerClosure

/-!
概要：有限環拡大の余核の台から、中心の冪を導手に入れる。
方針：像による商加群の零化を、部分環の導手の定義へ移す。
規約：中心外の同型から台の包含を得る段は別に接続する。
使われ方：有限射の Frobenius 順極限の四角形。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
universe u v
variable {A : Type u} {B : Type v} [CommRing A] [CommRing B]
variable [Algebra A B] [Module.Finite A B]

/-- 有限環拡大の余核の台が中心内なら、中心のある冪の拡大は導手に含まれる。 -/
theorem finiteSupport_exists_pow_map_le_conductor (I : Ideal A) (hI : I.FG)
    (h : Module.support A (B ⧸ LinearMap.range (Algebra.linearMap A B)) ⊆
      PrimeSpectrum.zeroLocus (I : Set A)) :
    ∃ n : ℕ, (I ^ n).map (algebraMap A B) ≤
      SerrePositivity.CommutativeAlgebra.subringConductor (algebraMap A B).range := by
  obtain ⟨n, hn⟩ := finiteQuotientSupport_exists_pow_smul_mem B
    (LinearMap.range (Algebra.linearMap A B)) I hI h
  refine ⟨n, Ideal.map_le_iff_le_comap.mpr ?_⟩
  intro a ha
  change ∀ b : B, algebraMap A B a * b ∈ (algebraMap A B).range
  intro b
  obtain ⟨c, hc⟩ := hn a ha b
  exact ⟨c, by simpa only [Algebra.linearMap_apply, Algebra.smul_def] using hc⟩

/-- 中心の冪の拡大の各元は、元の環に持ち上がる。 -/
theorem finiteSupport_exists_pow_map_lift (I : Ideal A) (hI : I.FG)
    (h : Module.support A (B ⧸ LinearMap.range (Algebra.linearMap A B)) ⊆
      PrimeSpectrum.zeroLocus (I : Set A)) :
    ∃ n : ℕ, ∀ b ∈ (I ^ n).map (algebraMap A B), ∃ a : A, algebraMap A B a = b := by
  obtain ⟨n, hn⟩ := finiteSupport_exists_pow_map_le_conductor I hI h
  exact ⟨n, fun b hb ↦
    SerrePositivity.CommutativeAlgebra.subringConductor_le (algebraMap A B).range (hn hb)⟩

end SerrePositivity.AlgebraicGeometry
