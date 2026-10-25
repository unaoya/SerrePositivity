module

public import SerrePositivity.BhattScholze.Prism.WittQuotientTiltKernel
public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # 完備な係数環からWitt商tiltへの全射性

F6の核計算と、tiltの座標からの分離性を使う。
Witt商のp正則性やFontaine核の単項性を仮定しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]
variable (d : WittVector p k) [Fact (¬ IsUnit (p : WittVector p k ⧸ Ideal.span {d}))]

/-- d₀の標準tilt像のイデアル進分離性は、各座標の冪零性から従う。 -/
theorem wittQuotientTilt_image_isHausdorff :
    IsHausdorff (Ideal.span {wittQuotientTiltMap p k d (d.coeff 0)})
      (PreTilt (WittVector p k ⧸ Ideal.span {d}) p) := by
  refine ⟨fun x hx ↦ ?_⟩
  apply Perfection.ext
  intro n
  let r := wittQuotientTiltMap p k d (d.coeff 0)
  have hm := hx (p ^ n)
  simp only [SModEq.sub_mem, sub_zero, smul_eq_mul, Ideal.mul_top,
    Ideal.span_singleton_pow] at hm
  obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hm
  change PreTilt.coeff n x = 0
  rw [hy, map_mul, map_pow]
  have he : PreTilt.coeff n r ^ (p ^ n) = PreTilt.coeff 0 r := by
    simpa only [zero_add] using compatibleRoots_pow p (fun i ↦ PreTilt.coeff i r)
      (fun i ↦ PreTilt.coeff_pow_p r i) 0 n
  rw [he, wittQuotientTiltMap_coeff_zero_d, zero_mul]

/-- 係数環がd₀進前完備なら標準tilt射は全射。一般の零因子d₀を許す。 -/
theorem wittQuotientTiltMap_surjective [IsPrecomplete (Ideal.span {d.coeff 0}) k] :
    Function.Surjective (wittQuotientTiltMap p k d) := by
  let S := WittVector p k ⧸ Ideal.span {d}
  let L := wittQuotientTiltMap p k d
  let I : Ideal k := Ideal.span {d.coeff 0}
  let K : Ideal (PreTilt S p) := Ideal.span {L (d.coeff 0)}
  have hmap : I.map L = K := by rw [Ideal.map_span, Set.image_singleton]
  let : IsHausdorff (I.map L) (PreTilt S p) := by
    rw [hmap]
    exact wittQuotientTilt_image_isHausdorff p k d
  apply surjective_of_mk_map_comp_surjective (I := I) L
  let q : PreTilt S p →+* ModP S p := PreTilt.coeff 0
  have hker : RingHom.ker q = K := wittQuotientTilt_coeff_zero_kernel_eq_span_general p k d
  have hq : Function.Surjective q := Perfection.coeff_surjective
    ((wittDeltaStructure_isPerfect p k).quotient_mod_p_frobenius_surjective (Ideal.span {d})) 0
  let e : PreTilt S p ⧸ K ≃+* ModP S p :=
    (Ideal.quotEquivOfEq hker.symm).trans (RingHom.quotientKerEquivOfSurjective hq)
  have he (x : PreTilt S p) : e (Ideal.Quotient.mk K x) = q x := rfl
  rw [hmap]
  intro z
  obtain ⟨a, ha⟩ := wittQuotientCoefficientMap_surjective p k d (e z)
  refine ⟨a, e.injective ?_⟩
  change e (Ideal.Quotient.mk K (L a)) = e z
  rw [he]
  exact ha

end SerrePositivity.BhattScholze
