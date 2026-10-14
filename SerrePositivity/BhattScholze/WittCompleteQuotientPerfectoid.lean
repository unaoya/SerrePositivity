module

public import SerrePositivity.BhattScholze.WittQuotientTiltEquiv
public import SerrePositivity.BhattScholze.DistinguishedQuotientComplete
public import SerrePositivity.CommutativeAlgebra.StrictPRecovery

/-! # 完備なdistinguished Witt商の一般perfectoid性

F4/F5/F6の接続。標準Fontaine比較射の全単射性から核を直接移す。
商のp正則性・第0係数の正則性・F7の核進分離性を仮定しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze
variable (p : ℕ) [Fact p.Prime] (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]
variable (d : WittVector p k) [IsAdicComplete (Ideal.span {d}) (WittVector p k)]

section Nonunit
variable [Fact (¬ IsUnit (p : WittVector p k ⧸ Ideal.span {d}))]
variable [IsAdicComplete (Ideal.span {(p : WittVector p k ⧸ Ideal.span {d})})
  (WittVector p k ⧸ Ideal.span {d})]

/-- 一般の完備distinguished Witt商の標準Fontaine比較射は全単射。 -/
theorem wittCompleteQuotientFontaineMap_bijective
    (hd : (wittDeltaStructure p k).IsDistinguished d) :
    Function.Bijective (wittQuotientFontaineMap p k d) := by
  have h := wittQuotientTiltMap_bijective p k d hd
  exact ⟨WittVector.map_injective _ h.1, WittVector.map_surjective _ h.2⟩

/-- 一般商のFontaine核は、具体的な標準比較射によるdの像で生成される。 -/
theorem wittCompleteQuotient_fontaine_kernel_eq_span
    (hd : (wittDeltaStructure p k).IsDistinguished d) :
    RingHom.ker (WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p) =
      Ideal.span {wittQuotientFontaineMap p k d d} := by
  have h := Ideal.map_comap_of_surjective (wittQuotientFontaineMap p k d)
    (wittCompleteQuotientFontaineMap_bijective p k d hd).2
    (RingHom.ker (WittVector.fontaineTheta (WittVector p k ⧸ Ideal.span {d}) p))
  rw [wittQuotientFontaineMap_comap_kernel p k d, Ideal.map_span, Set.image_singleton] at h
  exact h.symm

end Nonunit

/-- d進完備なWitt環のdistinguished商は、一般のpねじれを許して整perfectoid。零環も含む。 -/
theorem wittCompleteDistinguishedQuotient_isIntegralPerfectoid
    (hd : (wittDeltaStructure p k).IsDistinguished d) :
    IsIntegralPerfectoid (WittVector p k ⧸ Ideal.span {d}) p := by
  let S := WittVector p k ⧸ Ideal.span {d}
  rcases subsingleton_or_nontrivial S with hs | hn
  · exact Or.inl hs
  · let := hn
    let : IsAdicComplete (Ideal.span {(p : S)}) S :=
      (wittDeltaStructure_isPerfect p k).distinguished_quotient_isAdicComplete hd
    have hp : ¬ IsUnit (p : S) := by
      intro hu
      let : Subsingleton S := subsingleton_of_isUnit_natCast_of_isHausdorff p S hu
      exact zero_ne_one (Subsingleton.elim (0 : S) 1)
    let : Fact (¬ IsUnit (p : S)) := ⟨hp⟩
    refine Or.inr ⟨hp, inferInstance,
      witt_distinguished_quotient_exists_unit_mul_pow_p p k d hd,
      (wittDeltaStructure_isPerfect p k).quotient_mod_p_frobenius_surjective (Ideal.span {d}), ?_⟩
    rw [wittCompleteQuotient_fontaine_kernel_eq_span p k d hd]
    infer_instance

end SerrePositivity.BhattScholze
