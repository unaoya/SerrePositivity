module

public import SerrePositivity.FieldTheory.PAdjoinDerivation
public import Mathlib.FieldTheory.IntermediateField.Algebraic
public import Mathlib.Data.Nat.Find

/-! # 有限な指数1の体拡大の微分の定数

任意の元のp乗が底体に属する有限拡大では、普遍微分が零になる元は底体の像そのもの。
指定元を避ける最大中間体を拡大次数の最小化で選び、次数pの導分を実構成する。
底体や終域の有限p-rankは要求しない。
-/

@[expose] public noncomputable section
namespace SerrePositivity
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
  obtain ⟨δ, hδ⟩ := exists_derivation_primeRoot_of_adjoin_eq_top x a ha hxE hs
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

end SerrePositivity
