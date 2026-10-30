-- lake build の後、lake env lean scripts/audit_f6.lean で実行する。
import SerrePositivity.CommutativeAlgebra.Perfection
import Mathlib.Util.AssertNoSorry

open SerrePositivity
universe u

-- BS F6の正確な型。aの正則性・Noether性・整域性を要求しない。
theorem f6_audit_bs_signature (k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime]
    [CharP k p] [PerfectRing k p] (a : k) [CharP (k ⧸ Ideal.span {a}) p] :
    RingHom.ker (Perfection.coeff (k ⧸ Ideal.span {a}) p 0) =
      Ideal.span {((Perfection.lift p k (k ⧸ Ideal.span {a}))
        (Ideal.Quotient.mk (Ideal.span {a}))) a} :=
  perfection_lift_principal_quotient_kernel k p a

-- 積環の標数は座標で判定する。
theorem f6_audit_product_source_charP (k : Type u) [CommRing k] (p : ℕ) [CharP k p] :
    CharP (k × k) p where
  cast_eq_zero_iff n := by
    have he : (n : k × k) = 0 ↔ (n : k) = 0 := by
      constructor
      · exact fun h ↦ congrArg Prod.fst h
      · intro h
        exact Prod.ext h h
    exact he.trans (CharP.cast_eq_zero_iff k p n)

-- 非正則な具体的生成元(1,0)を持つ積環の商にCharPを供給する。
theorem f6_audit_product_charP (k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime]
    [CharP k p] : CharP ((k × k) ⧸ Ideal.span {((1, 0) : k × k)}) p := by
  have := f6_audit_product_source_charP k p
  apply CharP.quotient' p
  intro n hn
  obtain ⟨t, ht⟩ := Ideal.mem_span_singleton.mp hn
  have he : (n : k) = 0 := by
    have h := congrArg Prod.snd ht
    simpa using h
  exact Prod.ext he he

theorem f6_audit_product_generator_nonregular (k : Type u) [CommRing k] [Nontrivial k] :
    ¬ Function.Injective (fun x : k × k ↦ (1, 0) * x) := by
  intro h
  have he : ((0, 1) : k × k) = 0 := h (by ext <;> simp)
  have hz := congrArg Prod.snd he
  exact one_ne_zero hz

-- 正則性のない積環でも公開核定理を適用できる。
theorem f6_audit_product_kernel (k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime]
    [CharP k p] [PerfectRing k p] :
    letI := f6_audit_product_source_charP k p
    letI := f6_audit_product_charP k p
    RingHom.ker (Perfection.coeff ((k × k) ⧸ Ideal.span {((1, 0) : k × k)}) p 0) =
      Ideal.span {principalQuotientPerfectionLift (k × k) p (1, 0) (1, 0)} := by
  have := f6_audit_product_source_charP k p
  have := f6_audit_product_charP k p
  exact perfection_principal_quotient_coeff_zero_kernel_eq_span (k × k) p (1, 0)

-- 旧APIの消滅条件の場合はJ=0で同じ生成公式になる。
theorem f6_audit_old_division (R : Type u) [CommRing R] (p : ℕ) [Fact p.Prime]
    [CharP R p] (d x : Perfection R p)
    (hdiv : ∀ n, Perfection.coeff R p n d ∣ Perfection.coeff R p n x)
    (hann : ∀ n z, Perfection.coeff R p (n + 1) d * z = 0 → z ^ p = 0) : d ∣ x := by
  apply perfection_dvd_of_coeff_dvd_of_ideal_correction R p d x ⊥
  · intro u
    refine ⟨0, ?_⟩
    have hu : (u : R) = 0 := u.property
    simp [hu, zero_pow (Fact.out : p.Prime).ne_zero]
  · intro n z hz
    have he : z = 0 := hz
    simp [he]
  · exact hdiv
  · intro n z hz
    exact hann n z hz

assert_no_sorry f6_audit_bs_signature
assert_no_sorry f6_audit_product_charP
assert_no_sorry f6_audit_product_generator_nonregular
assert_no_sorry f6_audit_product_kernel
assert_no_sorry f6_audit_old_division

assert_no_sorry f6_audit_product_source_charP
