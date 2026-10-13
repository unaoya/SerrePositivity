module

public import SerrePositivity.CommutativeAlgebra.WittCoefficientEmbedding
public import SerrePositivity.CommutativeAlgebra.PerfectNilpotentLifting
public import Mathlib.RingTheory.Perfectoid.FontaineTheta

/-! # 完全剰余体のWitt係数写像の実構成

D/(p)で完全剰余体のsectionを構成し、Perfectionへの普遍持ち上げと
既存のFontaineのθ写像を合成する。Dのperfectoid性は仮定しない。
-/

public section
namespace SerrePositivity
open IsLocalRing

/-- 完全剰余体を持つ完備Noether局所環には、剰余写像と両立するWitt係数写像が存在する。
標数零・整域性は写像の存在には不要。 -/
theorem exists_wittVector_residue_lift
    (D : Type*) [CommRing D] [IsLocalRing D] [IsNoetherianRing D]
    [IsAdicComplete (maximalIdeal D) D]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)] :
    ∃ f : WittVector p (ResidueField D) →+* D,
      (residue D).comp f = WittVector.constantCoeff := by
  let P : Ideal D := Ideal.span {(p : D)}
  have hP : P ≤ maximalIdeal D := by
    rw [Ideal.span_singleton_le_iff_mem, ← residue_eq_zero_iff]
    simp only [map_natCast, CharP.cast_eq_zero]
  let : Fact (¬ IsUnit (p : D)) := ⟨by
    simpa only [← mem_nonunits_iff, ← mem_maximalIdeal] using
      hP (Ideal.mem_span_singleton_self (p : D))⟩
  let : IsAdicComplete P D := isAdicComplete_span_residue_characteristic D p
  let q : ModP D p →+* ResidueField D :=
    Ideal.Quotient.lift P (residue D) (fun r hr ↦ (residue_eq_zero_iff r).mpr (hP hr))
  have hq : Function.Surjective q := by
    intro x
    obtain ⟨r, rfl⟩ := residue_surjective (R := D) x
    exact ⟨Ideal.Quotient.mk P r, rfl⟩
  have hker : RingHom.ker q = (maximalIdeal D).map (Ideal.Quotient.mk P) := by
    exact (Ideal.ker_quotient_lift (residue D)
      (show P ≤ RingHom.ker (residue D) by rw [ker_residue]; exact hP)).trans
      (congrArg (fun J : Ideal D ↦ J.map (Ideal.Quotient.mk P)) ker_residue)
  let : IsAdicComplete (maximalIdeal D) (ModP D p) :=
    isAdicComplete_finite (R := D) (ModP D p)
  let : IsAdicComplete (RingHom.ker q) (ModP D p) := by
    rw [hker]
    exact (IsAdicComplete.map_algebraMap_iff (maximalIdeal D) (ModP D p)).mpr
      inferInstance
  obtain ⟨s, hs, _⟩ := exists_unique_ringHom_lift_of_complete_kernel p q hq
    (RingHom.id (ResidueField D))
  let t : ResidueField D →+* PreTilt D p :=
    Perfection.lift p (ResidueField D) (ModP D p) s
  let f := (WittVector.fontaineTheta D p).comp (WittVector.map t)
  refine ⟨f, ?_⟩
  ext x
  change residue D (WittVector.fontaineTheta D p (WittVector.map t x)) = x.coeff 0
  have hm := congrArg q (WittVector.mk_fontaineTheta (WittVector.map t x))
  change residue D (WittVector.fontaineTheta D p (WittVector.map t x)) =
    q (Perfection.coeff (ModP D p) p 0 ((WittVector.map t x).coeff 0)) at hm
  rw [WittVector.map_coeff] at hm
  change residue D (WittVector.fontaineTheta D p (WittVector.map t x)) =
    q (s (x.coeff 0)) at hm
  exact hm.trans (RingHom.congr_fun hs (x.coeff 0))

/-- 標数零では、構成したWitt係数写像は剰余写像と両立する局所的な埋め込みとなる。
整域性は、この係数埋め込みの段階では不要。 -/
theorem exists_wittVector_coefficient_embedding
    (D : Type*) [CommRing D] [IsLocalRing D] [IsNoetherianRing D] [CharZero D]
    [IsAdicComplete (maximalIdeal D) D]
    (p : ℕ) [Fact p.Prime] [CharP (ResidueField D) p] [PerfectField (ResidueField D)] :
    ∃ f : WittVector p (ResidueField D) →+* D,
      Function.Injective f ∧ IsLocalHom f ∧
        (residue D).comp f = WittVector.constantCoeff := by
  obtain ⟨f, hf⟩ := exists_wittVector_residue_lift D p
  exact ⟨f, wittVector_ringHom_injective p f, wittVector_ringHom_isLocalHom p f, hf⟩

end SerrePositivity
