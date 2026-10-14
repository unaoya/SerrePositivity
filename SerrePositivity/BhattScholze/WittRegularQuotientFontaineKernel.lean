module

public import SerrePositivity.BhattScholze.WittQuotientFontaineComparison
public import SerrePositivity.BhattScholze.WittRegularQuotientPerfectoid

/-! # 正則Witt商の標準比較射によるFontaine核の生成

存在だけでなく、元のdistinguished元dの標準Fontaine像が核を生成すると特定する。
商の古典的p完備性とd₀の正則性を明示したTheorem 3.10の部分定理。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]
variable (d : WittVector p k) [Fact (¬ IsUnit (p : WittVector p k ⧸ Ideal.span {d}))]
variable [IsAdicComplete (Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})})
  (WittVector p k ⧸ Ideal.span {d})]

/-- d₀が正則な完備distinguished Witt商の標準Fontaine核は、比較射のd像で生成される。 -/
theorem wittRegularQuotient_fontaine_kernel_eq_span_image
    (hd : (wittDeltaStructure p k).IsDistinguished d)
    (hreg : Function.Injective (fun x : k ↦ d.coeff 0 * x)) :
    RingHom.ker (WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p) =
      Ideal.span {wittQuotientFontaineMap p k d d} := by
  apply PerfectoidFrobeniusCriterion.ker_fontaineTheta_eq_span_of_firstCoeff_unit
    (WittVector p k ⧸ Ideal.span {d}) p
    (wittRegularQuotient_fontaine_kernel_isPrincipal p k d hd hreg)
    (wittQuotientFontaineMap p k d d)
    (wittQuotientFontaineMap_generator_mem_kernel p k d)
  have hu : IsUnit ((wittQuotientFontaineMap p k d d).coeff 1) :=
    (wittDeltaStructure_isDistinguished_iff p
      (PreTilt (WittVector p k ⧸ Ideal.span {d}) p) _).mp
        (wittQuotientFontaineMap_isDistinguished p k d hd)
  exact hu.map (PreTilt.coeff 0)

/-- 正則distinguished元の生成イデアルの標準Fontaine像は標準Fontaine核全体。 -/
theorem wittRegularQuotient_map_span_eq_fontaine_kernel
    (hd : (wittDeltaStructure p k).IsDistinguished d)
    (hreg : Function.Injective (fun x : k ↦ d.coeff 0 * x)) :
    (Ideal.span {d}).map (wittQuotientFontaineMap p k d) =
      RingHom.ker (WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p) := by
  rw [Ideal.map_span, Set.image_singleton,
    wittRegularQuotient_fontaine_kernel_eq_span_image p k d hd hreg]

end SerrePositivity.BhattScholze
