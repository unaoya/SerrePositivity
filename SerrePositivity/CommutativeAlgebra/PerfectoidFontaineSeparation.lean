module

public import SerrePositivity.CommutativeAlgebra.TiltRootSeparation
public import SerrePositivity.CommutativeAlgebra.WittPrincipalSeparation
public import SerrePositivity.CommutativeAlgebra.PerfectoidFrobeniusCriterion

/-! # p正則な整perfectoid環のFontaine核進分離性 -/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity
open PerfectoidFrobeniusCriterion
variable (S : Type u) [CommRing S] (p : ℕ) [Fact p.Prime]
    [Fact (¬ IsUnit (p : S))] [IsAdicComplete (Ideal.span {(p : S)}) S]

/-- pの根から得るprimitive形Witt元の主イデアル進分離性。 -/
theorem witt_primitive_isHausdorff_of_tilt_root (q : PreTilt S p) (u : Sˣ)
    (hp : (p : S) = u * q.untilt ^ p)
    (hq : Function.Injective (fun x : S ↦ q.untilt * x))
    (a : WittVector p (PreTilt S p)) (ha : IsUnit (a.coeff 0)) :
    IsHausdorff (Ideal.span {((p : WittVector p (PreTilt S p)) +
      WittVector.teichmuller p q ^ p * a)}) (WittVector p (PreTilt S p)) := by
  let d := (p : WittVector p (PreTilt S p)) + WittVector.teichmuller p q ^ p * a
  have hd : d.coeff 0 = q ^ p * a.coeff 0 := by
    change WittVector.constantCoeff d = _
    simp only [d, map_add, map_mul, map_pow, map_natCast,
      CharP.cast_eq_zero, zero_add, WittVector.constantCoeff_apply,
      WittVector.teichmuller_coeff_zero]
  have hqreg : IsLeftRegular q := tilt_mul_injective_of_untilt_regular S p q hq
  have hdreg : IsLeftRegular (d.coeff 0) := by
    rw [hd]
    exact (IsLeftRegular.pow p hqreg).mul ha.isRegular.left
  have : IsHausdorff (Ideal.span {q}) (PreTilt S p) :=
    tilt_isHausdorff_of_unit_untilt_root S p q u hp
  have hle : Ideal.span {d.coeff 0} ≤ Ideal.span {q} := by
    apply (Ideal.span_singleton_le_iff_mem _).mpr
    rw [hd]
    apply (Ideal.span {q}).mul_mem_right
    exact Ideal.pow_mem_of_mem _ (Ideal.mem_span_singleton_self q) p (Fact.out : p.Prime).pos
  have : IsHausdorff (Ideal.span {d.coeff 0}) (PreTilt S p) := by
    constructor
    intro x hx
    apply IsHausdorff.haus' (I := Ideal.span {q})
    intro n
    exact (hx n).mono (Submodule.smul_mono_left (pow_le_pow_left' hle n))
  exact witt_isHausdorff_of_constantCoeff (PreTilt S p) p d hdreg

/-- 単元倍p乗根・Frobenius全射・単項核を明示したFontaine核進分離性。 -/
theorem fontaine_kernel_isHausdorff_of_unit_root
    (hF : Function.Surjective (frobenius (ModP S p) p))
    (hker : (RingHom.ker (WittVector.fontaineTheta S p)).IsPrincipal)
    (π : S) (u : Sˣ) (hp : (p : S) = u * π ^ p)
    (hregular : Function.Injective (fun x : S ↦ (p : S) * x)) :
    IsHausdorff (RingHom.ker (WittVector.fontaineTheta S p))
      (WittVector p (PreTilt S p)) := by
  obtain ⟨q, v, a, hq, ha, hgen⟩ :=
    exists_untilt_unit_mul_and_unit_coefficient_kernel_generator S p hF hker π u hp
  have hπpow : IsLeftRegular (π ^ p) := by
    intro x y hxy
    apply hregular
    simpa only [hp, mul_assoc] using congrArg (fun z : S ↦ (u : S) * z) hxy
  have hπ : IsLeftRegular π := (IsLeftRegular.pow_iff (Fact.out : p.Prime).pos).mp hπpow
  have hqreg : IsLeftRegular q.untilt := by
    rw [hq]
    exact v.isUnit.isRegular.left.mul hπ
  have hpq : (p : S) = (u * (v⁻¹) ^ p : Sˣ) * q.untilt ^ p := by
    rw [hq, mul_pow, hp]
    simp only [Units.val_mul, Units.val_pow_eq_pow_val]
    have hv : (↑(v⁻¹) : S) ^ p * (v : S) ^ p = 1 := by
      rw [← mul_pow]
      simp
    calc
      _ = (u : S) * ((↑(v⁻¹) : S) ^ p * (v : S) ^ p) * π ^ p := by rw [hv]; simp
      _ = _ := by ring
  rw [hgen]
  exact witt_primitive_isHausdorff_of_tilt_root S p q (u * (v⁻¹) ^ p) hpq hqreg a ha

/-- F7：p正則な整perfectoid環のFontaine環はker θ進分離。 -/
theorem IsIntegralPerfectoid.fontaine_kernel_isHausdorff
    (hS : IsIntegralPerfectoid S p)
    (hregular : Function.Injective (fun x : S ↦ (p : S) * x)) :
    IsHausdorff (RingHom.ker (WittVector.fontaineTheta S p))
      (WittVector p (PreTilt S p)) := by
  have hn : ¬ Subsingleton S := by
    intro hs
    have := hs
    apply (Fact.out : ¬ IsUnit (p : S))
    rw [Subsingleton.elim (p : S) 1]
    exact isUnit_one
  obtain ⟨_, _, ⟨π, u, hp⟩, hF, hker⟩ := hS.resolve_left hn
  exact fontaine_kernel_isHausdorff_of_unit_root S p hF hker π u hp hregular

end SerrePositivity
