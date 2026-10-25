module

public import SerrePositivity.BhattScholze.Prism.WittRegularQuotientFontaineKernel
public import SerrePositivity.BhattScholze.Delta.DistinguishedTorsion
public import SerrePositivity.BhattScholze.Delta.PerfectDeltaFrobenius
public import Mathlib.RingTheory.AdicCompletion.Functoriality

/-! # Witt商の標準Fontaine比較射の単射性と同型条件

著者公開版Theorem 3.10の台環比較に向けた具体的な定理。
源のd進分離性で単射性を証明し、全射性には標的の核進分離性を明示する。
その分離性自体や一般Witt復元を未証明入力で置き換えない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]
variable (d : WittVector p k) [Fact (¬ IsUnit (p : WittVector p k ⧸ Ideal.span {d}))]

/-- distinguished元の標準Fontaine像は、完全Witt環で非零因子。
源のd₀正則性・d進完備性や商のp完備性は不要。 -/
theorem wittQuotientFontaineMap_generator_mul_injective
    (hd : (wittDeltaStructure p k).IsDistinguished d) :
    Function.Injective (fun x : WittVector p (PreTilt (WittVector p k ⧸ Ideal.span {d}) p) ↦
      wittQuotientFontaineMap p k d d * x) := by
  have hperfect := wittDeltaStructure_isPerfect p (PreTilt (WittVector p k ⧸ Ideal.span {d}) p)
  exact hperfect.distinguished_mul_injective
    (wittQuotientFontaineMap_isDistinguished p k d hd)

variable [IsAdicComplete (Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})})
  (WittVector p k ⧸ Ideal.span {d})]

/-- 標準Fontaine比較射の核の元は、源の(d)のすべての冪に属する。 -/
theorem wittQuotientFontaineMap_kernel_mem_pow
    (hd : (wittDeltaStructure p k).IsDistinguished d) (n : ℕ) (x : WittVector p k)
    (hx : wittQuotientFontaineMap p k d x = 0) : x ∈ Ideal.span {d} ^ n := by
  induction n generalizing x with
  | zero => simp
  | succ n ih =>
    have hxI : x ∈ Ideal.span {d} := by
      rw [← wittQuotientFontaineMap_comap_kernel p k d]
      change WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p
        (wittQuotientFontaineMap p k d x) = 0
      rw [hx, map_zero]
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp hxI
    have hyker : wittQuotientFontaineMap p k d y = 0 := by
      apply wittQuotientFontaineMap_generator_mul_injective p k d hd
      change wittQuotientFontaineMap p k d d * wittQuotientFontaineMap p k d y =
        wittQuotientFontaineMap p k d d * 0
      rw [mul_zero, ← map_mul, ← hy, hx]
    rw [hy, pow_succ']
    exact Ideal.mul_mem_mul (Ideal.subset_span (Set.mem_singleton _)) (ih y hyker)

/-- 源がd進分離なら、distinguished商の標準Fontaine比較射は単射。
d₀の正則性は要求しない。 -/
theorem wittQuotientFontaineMap_injective
    [IsHausdorff (Ideal.span {d}) (WittVector p k)]
    (hd : (wittDeltaStructure p k).IsDistinguished d) :
    Function.Injective (wittQuotientFontaineMap p k d) := by
  apply (injective_iff_map_eq_zero (wittQuotientFontaineMap p k d)).mpr
  intro x hx
  apply IsHausdorff.haus' (I := Ideal.span {d}) x
  intro n
  apply SModEq.sub_mem.mpr
  simpa only [sub_zero, smul_eq_mul, Ideal.mul_top] using
    wittQuotientFontaineMap_kernel_mem_pow p k d hd n x hx

/-- 同じ仮定のもとで標準tilt射も単射。Teichmüller元でWitt比較射の単射性を使う。 -/
theorem wittQuotientTiltMap_injective
    [IsHausdorff (Ideal.span {d}) (WittVector p k)]
    (hd : (wittDeltaStructure p k).IsDistinguished d) :
    Function.Injective (wittQuotientTiltMap p k d) := by
  intro x y hxy
  have h : WittVector.teichmuller p x = WittVector.teichmuller p y := by
    apply wittQuotientFontaineMap_injective p k d hd
    change WittVector.map (wittQuotientTiltMap p k d) (WittVector.teichmuller p x) =
      WittVector.map (wittQuotientTiltMap p k d) (WittVector.teichmuller p y)
    rw [WittVector.map_teichmuller, WittVector.map_teichmuller, hxy]
  simpa only [WittVector.teichmuller_coeff_zero] using congrArg (fun z ↦ z.coeff 0) h

/-- 正則d₀の商では、源のd進前完備性と標的のFontaine核進分離性から比較射は全射。
核進分離性は明示的な仮定であり、perfectoid性だけから自動的に供給しない。 -/
theorem wittRegularQuotientFontaineMap_surjective
    [IsPrecomplete (Ideal.span {d}) (WittVector p k)]
    [IsHausdorff (RingHom.ker (WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p))
      (WittVector p (PreTilt (WittVector p k ⧸ Ideal.span {d}) p))]
    (hd : (wittDeltaStructure p k).IsDistinguished d)
    (hreg : Function.Injective (fun x : k ↦ d.coeff 0 * x)) :
    Function.Surjective (wittQuotientFontaineMap p k d) := by
  have heq := wittRegularQuotient_map_span_eq_fontaine_kernel p k d hd hreg
  let : IsHausdorff ((Ideal.span {d}).map (wittQuotientFontaineMap p k d))
      (WittVector p (PreTilt (WittVector p k ⧸ Ideal.span {d}) p)) := by
    rw [heq]
    infer_instance
  apply surjective_of_mk_map_comp_surjective (I := Ideal.span {d})
    (wittQuotientFontaineMap p k d)
  rw [heq]
  change Function.Surjective ((wittQuotientFontaineQuotientMap p k d).comp
    (Ideal.Quotient.mk (Ideal.span {d})))
  exact (wittQuotientFontaineQuotientMap_bijective p k d).2.comp Ideal.Quotient.mk_surjective

/-- 明示した二つのadic条件を持つ正則distinguished Witt商の標準比較射は全単射。 -/
theorem wittRegularQuotientFontaineMap_bijective
    [IsAdicComplete (Ideal.span {d}) (WittVector p k)]
    [IsHausdorff (RingHom.ker (WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p))
      (WittVector p (PreTilt (WittVector p k ⧸ Ideal.span {d}) p))]
    (hd : (wittDeltaStructure p k).IsDistinguished d)
    (hreg : Function.Injective (fun x : k ↦ d.coeff 0 * x)) :
    Function.Bijective (wittQuotientFontaineMap p k d) :=
  ⟨wittQuotientFontaineMap_injective p k d hd,
    wittRegularQuotientFontaineMap_surjective p k d hd hreg⟩

variable [IsAdicComplete (Ideal.span {d}) (WittVector p k)]
variable [IsHausdorff
  (RingHom.ker (WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p))
  (WittVector p (PreTilt (WittVector p k ⧸ Ideal.span {d}) p))]

/-- 明示したadic条件のもとで構成する、元のWitt環とFontaine環の具体的な同型。 -/
def wittRegularQuotientFontaineEquiv
    (hd : (wittDeltaStructure p k).IsDistinguished d)
    (hreg : Function.Injective (fun x : k ↦ d.coeff 0 * x)) :
    WittVector p k ≃+* WittVector p (PreTilt (WittVector p k ⧸ Ideal.span {d}) p) :=
  RingEquiv.ofBijective (wittQuotientFontaineMap p k d)
    (wittRegularQuotientFontaineMap_bijective p k d hd hreg)

/-- 同型の台環射は既に構成した標準Fontaine比較射。 -/
@[simp] theorem wittRegularQuotientFontaineEquiv_toRingHom
    (hd : (wittDeltaStructure p k).IsDistinguished d)
    (hreg : Function.Injective (fun x : k ↦ d.coeff 0 * x)) :
    (wittRegularQuotientFontaineEquiv p k d hd hreg).toRingHom =
      wittQuotientFontaineMap p k d := rfl

/-- 構成した同型の逆も標準Witt δ構造を保存する。 -/
theorem wittRegularQuotientFontaineEquiv_symm_isDeltaHom
    (hd : (wittDeltaStructure p k).IsDistinguished d)
    (hreg : Function.Injective (fun x : k ↦ d.coeff 0 * x)) :
    (wittDeltaStructure p (PreTilt (WittVector p k ⧸ Ideal.span {d}) p)).IsDeltaHom
      (wittDeltaStructure p k)
      (wittRegularQuotientFontaineEquiv p k d hd hreg).symm.toRingHom :=
  DeltaStructure.IsDeltaHom.symm (wittQuotientFontaineMap_isDeltaHom p k d)

/-- 逆比較射と元の標準商射の合成は、標準Fontaine射と一致する。 -/
theorem wittRegularQuotientFontaineEquiv_symm_comp_quotient
    (hd : (wittDeltaStructure p k).IsDistinguished d)
    (hreg : Function.Injective (fun x : k ↦ d.coeff 0 * x)) :
    (Ideal.Quotient.mk (Ideal.span {d})).comp
      (wittRegularQuotientFontaineEquiv p k d hd hreg).symm.toRingHom =
      WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p := by
  let e := wittRegularQuotientFontaineEquiv p k d hd hreg
  apply RingHom.ext
  intro x
  obtain ⟨y, rfl⟩ := e.surjective x
  change Ideal.Quotient.mk (Ideal.span {d}) (e.symm (e y)) =
    WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p (e y)
  rw [e.symm_apply_apply]
  exact (RingHom.congr_fun (wittQuotientFontaineMap_comp_fontaineTheta p k d) y).symm

end SerrePositivity.BhattScholze
