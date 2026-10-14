module

public import SerrePositivity.CommutativeAlgebra.CompatibleRootsTilt
public import SerrePositivity.CommutativeAlgebra.PerfectoidFontainePrincipal

/-! # 両立するp冪根と最初のFrobenius核からperfectoid性を導く

指定した根の列からtiltの元を構成するので、任意のuntiltの単元倍に対する
核計算を別に仮定する必要はない。Fontaine核の生成元をp-[pの根]として明示する。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable (S : Type*) [CommRing S] (p : ℕ) [Fact p.Prime]
    [Fact (¬ IsUnit (p : S))] [IsAdicComplete (Ideal.span {(p : S)}) S]

/-- pの両立する根と最初のFrobenius核から、Fontaine核の生成元を明示する。 -/
theorem fontaine_kernel_eq_span_of_compatible_p_roots
    (hregular : Function.Injective (fun x : S ↦ (p : S) * x))
    (hF : Function.Surjective (frobenius (ModP S p) p))
    (ρ : ℕ → S) (hρ0 : ρ 0 = (p : S)) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hker : ∀ z : ModP S p, z ^ p = 0 ↔ z ∈
      Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : S)}) (ρ 1)}) :
    RingHom.ker (WittVector.fontaineTheta S p) =
      Ideal.span {(p : WittVector p (PreTilt S p)) -
        WittVector.teichmuller p (compatibleRootsTilt S p (fun n ↦ ρ (n + 1))
          (fun n ↦ hρ (n + 1))) ^ p} := by
  let q := compatibleRootsTilt S p (fun n ↦ ρ (n + 1)) (fun n ↦ hρ (n + 1))
  have hqu : q.untilt = ρ 1 := compatibleRootsTilt_untilt S p _ _
  have hqp : q ^ p = compatibleRootsTilt S p ρ hρ := by
    apply Perfection.ext
    intro n
    change (Ideal.Quotient.mk (Ideal.span {(p : S)}) (ρ (n + 1))) ^ p =
      Ideal.Quotient.mk (Ideal.span {(p : S)}) (ρ n)
    rw [← map_pow, hρ]
  have htilt : RingHom.ker (PreTilt.coeff 0 : PreTilt S p →+* ModP S p) =
      Ideal.span {q ^ p} := by
    rw [hqp]
    exact compatibleRootsTilt_coeff_zero_kernel S p hregular hF ρ hρ0 hρ hker
  have ha : IsUnit ((-1 : WittVector p (PreTilt S p)).coeff 0) := by
    change IsUnit ((WittVector.constantCoeff : WittVector p (PreTilt S p) →+* _) (-1))
    exact isUnit_neg_one.map _
  have hξ : WittVector.fontaineTheta S p
      ((p : WittVector p (PreTilt S p)) + WittVector.teichmuller p q ^ p * (-1)) = 0 := by
    rw [map_add, map_mul, map_natCast, map_pow, map_neg, map_one,
      WittVector.fontaineTheta_teichmuller, hqu, hρ 0, hρ0]
    ring
  simpa only [mul_neg_one, sub_eq_add_neg] using
    PerfectoidFrobeniusCriterion.ker_fontaineTheta_eq_span_of_tilt_coeff_kernel
      S p hregular q (-1) ha hξ htilt

/-- p進完備でp正則な環のperfectoid性を、両立する根と最初のFrobenius核から判定する。 -/
theorem isIntegralPerfectoid_of_compatible_p_roots
    (hregular : Function.Injective (fun x : S ↦ (p : S) * x))
    (hF : Function.Surjective (frobenius (ModP S p) p))
    (ρ : ℕ → S) (hρ0 : ρ 0 = (p : S)) (hρ : ∀ n, ρ (n + 1) ^ p = ρ n)
    (hker : ∀ z : ModP S p, z ^ p = 0 ↔ z ∈
      Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : S)}) (ρ 1)}) :
    IsIntegralPerfectoid S p := by
  refine Or.inr ⟨Fact.out, inferInstance, ⟨ρ 1, 1, ?_⟩, hF, ?_⟩
  · simpa only [Units.val_one, one_mul, hρ0] using (hρ 0).symm
  · rw [fontaine_kernel_eq_span_of_compatible_p_roots S p hregular hF ρ hρ0 hρ hker]
    infer_instance

end SerrePositivity
