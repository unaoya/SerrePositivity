module

public import SerrePositivity.FieldTheory.PAdjoinDerivation
public import SerrePositivity.FieldTheory.PBasisDifferentials
public import SerrePositivity.FieldTheory.PBasisComplement
public import SerrePositivity.FieldTheory.PIndependentSet
public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.Data.Nat.Find

/-! # 指数1の拡大の微分の定数

概要：指数1の拡大 `K/F`（すべての `y ^ p` が `F` に属する）では、`Ω_{K/F}` で `D x = 0 ⟺ x ∈ F`。
二つの場合を扱う。
- `K/F` が有限な場合：`x` を避ける最大の中間体 `E` を拡大次数の最小化で選ぶと、`x` は `E` 上で次数 p の
  p 乗根として全体を生成するので、`primeRootDerivation` で検出できる。共有限な部分体の版が使われる。
- `F = K^p`（`K` は有限でなくてよい）：`x` を含む p 基底を取り、その偏導分で検出する。
規約：底体や終域の有限 p-rank は要求しない。
使われ方：共有限な部分体上の相対微分の零判定（`kaehlerDifferential_finite_subfield_eq_zero_iff`）。
-/

@[expose] public noncomputable section
namespace SerrePositivity

section Finite

variable {F K : Type*} [Field F] [Field K] [Algebra F K] [Module.Finite F K]

/-- 有限体拡大で、底体の外の指定元を避ける最大中間体を選べる。 -/
theorem exists_maximal_intermediateField_not_mem (x : K)
    (hx : x ∉ Set.range (algebraMap F K)) :
    ∃ E : IntermediateField F K, x ∉ E ∧
      ∀ H : IntermediateField F K, E ≤ H → x ∉ H → H = E := by
  classical
  let P : ℕ → Prop := fun n ↦ ∃ E : IntermediateField F K,
    x ∉ E ∧ Module.finrank E K = n
  have hex : ∃ n, P n :=
    ⟨_, ⊥, fun h ↦ hx (IntermediateField.mem_bot.mp h), rfl⟩
  obtain ⟨E, hxe, hn⟩ := Nat.find_spec hex
  refine ⟨E, hxe, ?_⟩
  intro H hEH hxH
  apply (IntermediateField.eq_of_le_of_finrank_le' hEH ?_).symm
  rw [hn]
  exact Nat.find_min' hex ⟨H, hxH, rfl⟩

/-- 有限な指数1の拡大では、底体の外の元を1に送る底体上の導分が存在する。 -/
theorem exists_derivation_detecting_finite_exponentOne
    {p : ℕ} [Fact p.Prime] [CharP K p]
    (hpow : ∀ y : K, ∃ a : F, y ^ p = algebraMap F K a)
    (x : K) (hx : x ∉ Set.range (algebraMap F K)) :
    ∃ δ : Derivation F K K, δ x = 1 := by
  obtain ⟨E, hxe, hmax⟩ := exists_maximal_intermediateField_not_mem x hx
  have hpE (y : K) : ∃ a : E, y ^ p = algebraMap E K a := by
    obtain ⟨a, ha⟩ := hpow y
    exact ⟨algebraMap F E a, by simpa only [IsScalarTower.algebraMap_apply F E K] using ha⟩
  have hxE : x ∉ Set.range (algebraMap E K) := by
    rintro ⟨a, ha⟩
    exact hxe (ha ▸ a.property)
  obtain ⟨a, ha⟩ := hpE x
  have hdegx := finrank_adjoin_of_prime_pow_eq x a ha hxE
  have htop : IntermediateField.adjoin E {x} = ⊤ := by
    apply top_unique
    intro y _
    by_cases hy : y ∈ E
    · exact (IntermediateField.adjoin E {x}).algebraMap_mem ⟨y, hy⟩
    · let J := IntermediateField.adjoin E {y}
      let H := J.restrictScalars F
      have hEH : E ≤ H := fun z hz ↦ J.algebraMap_mem ⟨z, hz⟩
      have hyH : y ∈ H := IntermediateField.subset_adjoin E {y} (Set.mem_singleton y)
      have hxH : x ∈ H := by
        by_contra h
        have he := hmax H hEH h
        rw [he] at hyH
        exact hy hyH
      have hsub : IntermediateField.adjoin E {x} ≤ J :=
        IntermediateField.adjoin_le_iff.mpr (Set.singleton_subset_iff.mpr hxH)
      obtain ⟨b, hb⟩ := hpE y
      have hyE : y ∉ Set.range (algebraMap E K) := by
        rintro ⟨c, hc⟩
        exact hy (hc ▸ c.property)
      have hdegy := finrank_adjoin_of_prime_pow_eq y b hb hyE
      have heq := IntermediateField.eq_of_le_of_finrank_eq hsub (hdegx.trans hdegy.symm)
      have hyJ : y ∈ J := hyH
      rw [← heq] at hyJ
      exact hyJ
  have hs : Algebra.adjoin E {x} = ⊤ :=
    Algebra.adjoin_eq_top_of_intermediateField
      (fun y _ ↦ Algebra.IsAlgebraic.isAlgebraic y) htop
  let δ := primeRootDerivation x a ha hxE hs
  have hδ : δ x = 1 := primeRootDerivation_self x a ha hxE hs
  exact ⟨δ.restrictScalars F, hδ⟩

/-- 指数1の有限拡大の通常微分の零判定。 -/
theorem kaehlerDifferential_finite_exponentOne_eq_zero_iff
    {p : ℕ} [Fact p.Prime] [CharP K p]
    (hpow : ∀ y : K, ∃ a : F, y ^ p = algebraMap F K a) (x : K) :
    KaehlerDifferential.D F K x = 0 ↔ x ∈ Set.range (algebraMap F K) := by
  constructor
  · intro h
    by_contra hx
    obtain ⟨δ, hδ⟩ := exists_derivation_detecting_finite_exponentOne hpow x hx
    have he := congrArg δ.liftKaehlerDifferential h
    rw [Derivation.liftKaehlerDifferential_comp_D, hδ, map_zero] at he
    exact one_ne_zero he
  · rintro ⟨a, rfl⟩
    exact (KaehlerDifferential.D F K).map_algebraMap a

/-- p乗部分体を含む共有限な部分体について、相対微分が零であることと所属が同値。 -/
theorem kaehlerDifferential_finite_subfield_eq_zero_iff
    {p : ℕ} [Fact p.Prime] [CharP K p]
    (E : Subfield K) [Module.Finite E K] (hE : pPowerSubfield K p ≤ E) (x : K) :
    KaehlerDifferential.D E K x = 0 ↔ x ∈ E := by
  have hp (y : K) : ∃ a : E, y ^ p = algebraMap E K a :=
    ⟨⟨y ^ p, hE ((mem_pPowerSubfield K p _).mpr ⟨y, rfl⟩)⟩, rfl⟩
  rw [kaehlerDifferential_finite_exponentOne_eq_zero_iff hp]
  constructor
  · rintro ⟨a, rfl⟩
    exact a.property
  · intro h
    exact ⟨⟨x, h⟩, rfl⟩

end Finite

section Absolute

variable {K : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]

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

end Absolute

end SerrePositivity
