module

public import SerrePositivity.FieldTheory.PIndependentSet
public import SerrePositivity.FieldTheory.PBasisPartialDerivation

/-! # p乗部分体上の通常微分の定数

p乗でない元を含むp-basisを構成し、その偏導分で通常微分の非零性を検出する。
全p-basisの有限性は要求しない。一般の相対底体上の判定は別の課題。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]

/-- p乗でない指定した元を含む、実際のp-basisが存在する。 -/
theorem exists_pBasis_containing_of_not_mem_pPowerSubfield (x : K)
    (hx : x ∉ pPowerSubfield K p) :
    ∃ s : Set K, x ∈ s ∧ IsPBasis K p (Subtype.val : s → K) := by
  have hxe : x ∉ pMonomialIntermediateField (p := p) (Subtype.val : (∅ : Set K) → K) := by
    rw [pMonomialIntermediateField_eq_adjoin, Set.range_eq_empty, IntermediateField.adjoin_empty]
    intro h
    obtain ⟨c, hc⟩ := IntermediateField.mem_bot.mp h
    exact hx (hc ▸ c.property)
  have hs := (isPIndependentSet_empty (K := K) (p := p)).insert x hxe
  obtain ⟨s, hsub, hb⟩ := exists_pBasis_superset _ hs
  exact ⟨s, hsub (by simp), hb⟩

/-- p乗でない元を1に送る、p乗部分体上の導分が存在する。 -/
theorem exists_derivation_detecting_not_mem_pPowerSubfield (x : K)
    (hx : x ∉ pPowerSubfield K p) :
    ∃ δ : Derivation (pPowerSubfield K p) K K, δ x = 1 := by
  obtain ⟨s, hxs, hb⟩ := exists_pBasis_containing_of_not_mem_pPowerSubfield x hx
  exact ⟨hb.partialDerivation ⟨x, hxs⟩,
    by simpa using hb.partialDerivation_apply ⟨x, hxs⟩ ⟨x, hxs⟩⟩

/-- p乗部分体上では、通常の普遍微分が零であることとp乗であることが同値。 -/
theorem kaehlerDifferential_over_pPowers_eq_zero_iff (x : K) :
    KaehlerDifferential.D (pPowerSubfield K p) K x = 0 ↔ x ∈ pPowerSubfield K p := by
  constructor
  · intro h
    by_contra hx
    obtain ⟨δ, hδ⟩ := exists_derivation_detecting_not_mem_pPowerSubfield x hx
    have he := congrArg δ.liftKaehlerDifferential h
    rw [Derivation.liftKaehlerDifferential_comp_D, hδ, map_zero] at he
    exact one_ne_zero he
  · exact derivation_eq_zero_on_pPowerSubfield (KaehlerDifferential.D (pPowerSubfield K p) K) x

/-- p乗でない元を検出する共有限な中間体を、実際のp-basisの補中間体として選べる。
指定済みの部分体族からの選択は、この存在定理とは区別する。 -/
theorem exists_finite_intermediateField_detecting_not_mem_pPowerSubfield (x : K)
    (hx : x ∉ pPowerSubfield K p) :
    ∃ E : IntermediateField (pPowerSubfield K p) K,
      Module.Finite E K ∧ KaehlerDifferential.D E K x ≠ 0 := by
  obtain ⟨s, hxs, hb⟩ := exists_pBasis_containing_of_not_mem_pPowerSubfield x hx
  let i : s := ⟨x, hxs⟩
  let E := pBasisComplementField (p := p) (Subtype.val : s → K) i
  let a : E := ⟨x ^ p, E.algebraMap_mem
    ⟨x ^ p, (mem_pPowerSubfield K p _).mpr ⟨x, rfl⟩⟩⟩
  have hs : Algebra.adjoin E {x} = ⊤ := hb.adjoin_complement_eq_top i
  let B := PowerBasis.ofAdjoinEqTop (isIntegral_of_prime_pow_eq x a rfl) hs
  obtain ⟨δ, hδ, _⟩ := hb.exists_complementDerivation i
  refine ⟨E, B.finite, ?_⟩
  intro h
  have he := congrArg δ.liftKaehlerDifferential h
  rw [Derivation.liftKaehlerDifferential_comp_D, map_zero] at he
  exact one_ne_zero (hδ.symm.trans he)

end SerrePositivity
