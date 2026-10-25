module

public import SerrePositivity.BhattScholze.Prism.Perfectoid.WittQuotientTiltMap
public import SerrePositivity.CommutativeAlgebra.PerfectionPrincipalQuotientKernel

/-! # 一般のWitt主イデアル商のtilt射影核

受領F6をmod p商同型に沿って移す。第0係数の正則性は仮定しない。
p非単元の枝を扱い、商の零環にはCharP pを無条件に供給しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]
variable (d : WittVector p k) [Fact (¬ IsUnit (p : WittVector p k ⧸ Ideal.span {d}))]

/-- 一般のWitt商のtilt第0射影核はd₀の標準tilt像で生成される。零因子d₀を許す。 -/
theorem wittQuotientTilt_coeff_zero_kernel_eq_span_general :
    RingHom.ker (PreTilt.coeff 0 : PreTilt (WittVector p k ⧸ Ideal.span {d}) p →+*
      ModP (WittVector p k ⧸ Ideal.span {d}) p) =
        Ideal.span {wittQuotientTiltMap p k d (d.coeff 0)} := by
  let S := WittVector p k ⧸ Ideal.span {d}
  let Q := k ⧸ Ideal.span {d.coeff 0}
  let e := wittQuotientModPEquiv p k d
  let : CharP Q p := charP_of_injective_ringHom (f := e.toRingHom) e.injective p
  let L := (Perfection.lift p k Q) (Ideal.Quotient.mk (Ideal.span {d.coeff 0}))
  have hL : Perfection.map p e.symm.toRingHom (L (d.coeff 0)) =
      wittQuotientTiltMap p k d (d.coeff 0) := by
    apply Perfection.ext
    intro n
    rfl
  have hback (x : PreTilt S p) :
      Perfection.map p e.symm.toRingHom (Perfection.map p e.toRingHom x) = x := by
    apply Perfection.ext
    intro n
    exact e.symm_apply_apply _
  apply le_antisymm
  · intro x hx
    let y := Perfection.map p e.toRingHom x
    have hy : y ∈ RingHom.ker (Perfection.coeff Q p 0) := by
      change e (PreTilt.coeff 0 x) = 0
      rw [show PreTilt.coeff 0 x = 0 from hx, map_zero]
    rw [perfection_lift_principal_quotient_kernel k p (d.coeff 0)] at hy
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hy
    apply Ideal.mem_span_singleton.mpr
    refine ⟨Perfection.map p e.symm.toRingHom b, ?_⟩
    have h := congrArg (Perfection.map p e.symm.toRingHom) hb
    rw [map_mul, hL, hback] at h
    exact h
  · apply (Ideal.span_singleton_le_iff_mem _).mpr
    exact wittQuotientTiltMap_coeff_zero_d p k d

end SerrePositivity.BhattScholze
