module

public import SerrePositivity.FieldTheory.PAdjoin
public import SerrePositivity.FieldTheory.SubfieldSpanIntersection

/-! # 部分体族に一つのp乗根を添加した後の交わり

p乗部分体を含む下向き有向な部分体族では、交わりを取る操作と
一つの元の添加が可換になる。共通の冪基底の係数の一意性を使う。
-/

@[expose] public noncomputable section
namespace SerrePositivity
variable {K ι : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]

/-- p乗が部分体に属する元の添加は、p未満の冪の線形包そのもの。
元が既に底体に属する場合も含む。 -/
theorem mem_subfield_adjoin_primeRoot_iff
    (E : Subfield K) (a : K) (ha : a ^ p ∈ E) (z : K) :
    z ∈ IntermediateField.adjoin E {a} ↔
      z ∈ Submodule.span E (Set.range (fun i : Fin p ↦ a ^ (i : ℕ))) := by
  classical
  constructor
  · intro hz
    by_cases hmem : a ∈ E
    · have hbot : IntermediateField.adjoin E {a} = ⊥ := by
        rw [IntermediateField.adjoin_eq_bot_iff, Set.singleton_subset_iff]
        exact IntermediateField.mem_bot.mpr ⟨⟨a, hmem⟩, rfl⟩
      rw [hbot] at hz
      obtain ⟨c, rfl⟩ := IntermediateField.mem_bot.mp hz
      have h1 : (1 : K) ∈ Submodule.span E
          (Set.range (fun i : Fin p ↦ a ^ (i : ℕ))) := by
        exact Submodule.subset_span ⟨⟨0, (Fact.out : p.Prime).pos⟩, pow_zero a⟩
      simpa only [Algebra.smul_def, mul_one] using
        (Submodule.span E (Set.range (fun i : Fin p ↦ a ^ (i : ℕ)))).smul_mem c h1
    · let B := IntermediateField.adjoin.powerBasis
        (isIntegral_of_prime_pow_eq a (⟨a ^ p, ha⟩ : E) rfl)
      have hdim : B.dim = p := minpoly_natDegree_of_pow_eq a (⟨a ^ p, ha⟩ : E) rfl
        (by rintro ⟨c, hc⟩; exact hmem (hc ▸ c.property))
      rw [← hdim]
      apply (Submodule.mem_span_range_iff_exists_fun E).mpr
      refine ⟨fun i ↦ B.basis.repr ⟨z, hz⟩ i, ?_⟩
      have heq := congrArg (fun y : IntermediateField.adjoin E {a} ↦ (y : K))
        (B.basis.sum_repr ⟨z, hz⟩)
      simpa [B.basis_eq_pow, B, IntermediateField.adjoin.powerBasis_gen,
        Algebra.smul_def] using heq
  · intro hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact pow_mem (IntermediateField.mem_adjoin_simple_self E a) (i : ℕ)
    | zero => exact (IntermediateField.adjoin E {a}).zero_mem
    | add x y _ _ hx hy => exact (IntermediateField.adjoin E {a}).add_mem hx hy
    | smul c x _ hx => exact (IntermediateField.adjoin E {a}).smul_mem hx

/-- 下向き有向な部分体族への一元添加は交わりと可換。
有限拡大性も、有限p-rankも要求しない。 -/
theorem iInf_subfield_adjoin_primeRoot
    (E : ι → Subfield K)
    (hdir : ∀ i j, ∃ k, E k ≤ E i ∧ E k ≤ E j)
    (hpow : ∀ i, pPowerSubfield K p ≤ E i)
    (hinf : (⨅ i, E i) = pPowerSubfield K p)
    (a : K) (ha : a ∉ pPowerSubfield K p) :
    (⨅ i, (IntermediateField.adjoin (E i) {a}).toSubfield) =
      (IntermediateField.adjoin (pPowerSubfield K p) {a}).toSubfield := by
  classical
  have hap : a ^ p ∈ pPowerSubfield K p := (mem_pPowerSubfield K p _).mpr ⟨a, rfl⟩
  have hind : ∃ j, LinearIndependent (E j) (fun i : Fin p ↦ a ^ (i : ℕ)) := by
    have hex : ∃ j, a ∉ E j := by
      by_contra h
      apply ha
      rw [← hinf]
      exact Subfield.mem_iInf.mpr (by simpa only [not_exists, not_not] using h)
    obtain ⟨j, hj⟩ := hex
    exact ⟨j, linearIndependent_pow_of_prime_pow_eq a (⟨a ^ p, hpow j hap⟩ : E j) rfl
      (by rintro ⟨c, hc⟩; exact hj (hc ▸ c.property))⟩
  ext z
  simp only [Subfield.mem_iInf, IntermediateField.mem_toSubfield]
  simp_rw [mem_subfield_adjoin_primeRoot_iff _ a (hpow _ hap)]
  rw [mem_all_subfield_spans_iff E hdir _ hind, hinf]
  exact (mem_subfield_adjoin_primeRoot_iff (pPowerSubfield K p) a hap z).symm

end SerrePositivity
