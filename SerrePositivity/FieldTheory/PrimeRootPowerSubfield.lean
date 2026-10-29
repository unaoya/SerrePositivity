module

public import SerrePositivity.FieldTheory.PAdjoin
public import SerrePositivity.FieldTheory.SubfieldLinearAlgebra
public import Mathlib.RingTheory.PowerBasis
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra

/-! # p 乗根一つの添加と、p 乗部分体の族の交わり

概要：
- 単純添加と冪の線形包：`a` が `F` 上整で最小多項式の次数が `n` 以下なら、`F(a)` は `1, a, …, a^{n-1}` の
  `F` 上の線形包（Mathlib の `IsIntegral.mem_span_pow` の中間体版）。p 乗根（`a ^ p ∈ E`）は `n = p` の場合。
- 交わり：交わりが `K^p` の下向き有向な部分体族 `Eᵢ` について `⋂ Eᵢ(a) = K^p(a)`。
- p 乗部分体：`L = K(x)`、`x ^ p = a` なら `L^p` は `K^p(a)` の像で、添加の後も `⋂ (Eᵢ · L^p) = L^p`。
方針：共通の冪 `1, a, …, a^{p-1}` で線形包を書き、`mem_all_subfield_spans_iff` で交わりを計算する。
使われ方：有限拡大での p 乗部分体の族の交わりの帰納（`PowerSubfieldFamilyIntersection`）。
-/

@[expose] public noncomputable section
namespace SerrePositivity
open Polynomial

section SpanPow

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

/-- 整な元 `a` の最小多項式の次数が `n` 以下なら、`F(a)` は `1, a, …, a^{n-1}` の線形包。 -/
theorem mem_adjoin_simple_iff_mem_span_pow {a : K} (ha : IsIntegral F a) {n : ℕ}
    (hn : (minpoly F a).natDegree ≤ n) (z : K) :
    z ∈ IntermediateField.adjoin F {a} ↔
      z ∈ Submodule.span F (Set.range fun i : Fin n ↦ a ^ (i : ℕ)) := by
  constructor
  · intro hz
    have hz' : z ∈ Algebra.adjoin F {a} := by
      rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic ha.isAlgebraic]
      exact hz
    rw [Algebra.adjoin_singleton_eq_range_aeval] at hz'
    obtain ⟨f, rfl⟩ := hz'
    refine Submodule.span_mono ?_ (ha.mem_span_pow ⟨f, rfl⟩)
    rintro _ ⟨i, rfl⟩
    exact ⟨⟨i, i.isLt.trans_le hn⟩, rfl⟩
  · intro hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact pow_mem (IntermediateField.mem_adjoin_simple_self F a) (i : ℕ)
    | zero => exact (IntermediateField.adjoin F {a}).zero_mem
    | add x y _ _ hx hy => exact (IntermediateField.adjoin F {a}).add_mem hx hy
    | smul c x _ hx => exact (IntermediateField.adjoin F {a}).smul_mem hx

/-- `a ^ p` が `E` に入れば、`E(a)` は `1, a, …, a^{p-1}` の `E` 上の線形包。 -/
theorem mem_adjoin_simple_iff_mem_span_pow_of_pow_mem {p : ℕ} [Fact p.Prime]
    (E : Subfield K) (a : K) (ha : a ^ p ∈ E) (z : K) :
    z ∈ IntermediateField.adjoin E {a} ↔
      z ∈ Submodule.span E (Set.range fun i : Fin p ↦ a ^ (i : ℕ)) := by
  have hint := isIntegral_of_prime_pow_eq (F := E) a (⟨a ^ p, ha⟩ : E) rfl
  refine mem_adjoin_simple_iff_mem_span_pow hint ?_ z
  have hne : (X ^ p - C (⟨a ^ p, ha⟩ : E) : E[X]) ≠ 0 :=
    (monic_X_pow_sub_C _ (Fact.out : p.Prime).ne_zero).ne_zero
  calc (minpoly E a).natDegree ≤ (X ^ p - C (⟨a ^ p, ha⟩ : E)).natDegree :=
        natDegree_le_of_dvd (minpoly.dvd E a (by simp [Subfield.algebraMap_ofSubfield])) hne
    _ = p := natDegree_X_pow_sub_C

end SpanPow

section Intersection

variable {K ι : Type*} [Field K] {p : ℕ} [Fact p.Prime] [CharP K p]

/-- 下向き有向な部分体族への一元添加は交わりと可換。
有限拡大性も、有限p-rankも要求しない。 -/
theorem iInf_subfield_adjoin_primeRoot
    (E : ι → Subfield K)
    (hdir : Directed (· ≥ ·) E)
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
  simp_rw [mem_adjoin_simple_iff_mem_span_pow_of_pow_mem _ a (hpow _ hap)]
  rw [mem_all_subfield_spans_iff E hdir _ hind, hinf]
  exact (mem_adjoin_simple_iff_mem_span_pow_of_pow_mem (pPowerSubfield K p) a hap z).symm

end Intersection

section PowerSubfield

variable {K L ι : Type*} [Field K] [Field L] [Algebra K L]
  {p : ℕ} [Fact p.Prime] [CharP K p] [CharP L p]

/-- 単純なp乗根添加のp乗部分体を、底体内の係数の添加として計算する。
自明な添加も含み、拡大次数の仮定は不要。 -/
theorem pPowerSubfield_primeRoot_eq_map_adjoin
    (x : L) (a : K) (hpow : x ^ p = algebraMap K L a)
    (hs : Algebra.adjoin K {x} = ⊤) :
    pPowerSubfield L p =
      (IntermediateField.adjoin (pPowerSubfield K p) {a}).toSubfield.map (algebraMap K L) := by
  let T := (IntermediateField.adjoin (pPowerSubfield K p) {a}).toSubfield
  apply le_antisymm
  · intro y hy
    obtain ⟨z, rfl⟩ := (mem_pPowerSubfield L p y).mp hy
    clear hy
    have hz : z ∈ Algebra.adjoin K {x} := by rw [hs]; trivial
    induction hz using Algebra.adjoin_induction with
    | mem z hz =>
      have hzx : z = x := Set.mem_singleton_iff.mp hz
      rw [hzx, hpow]
      exact Subfield.mem_map.mpr ⟨a, IntermediateField.mem_adjoin_simple_self _ a, rfl⟩
    | algebraMap c =>
      rw [← map_pow]
      apply Subfield.mem_map.mpr
      refine ⟨c ^ p, ?_, rfl⟩
      exact (IntermediateField.adjoin (pPowerSubfield K p) {a}).algebraMap_mem
        ⟨c ^ p, (mem_pPowerSubfield K p _).mpr ⟨c, rfl⟩⟩
    | add z w _ _ hz hw =>
      change (frobenius L p) (z + w) ∈ T.map (algebraMap K L)
      rw [map_add]
      exact (T.map (algebraMap K L)).add_mem hz hw
    | mul z w _ _ hz hw =>
      rw [mul_pow]
      exact (T.map (algebraMap K L)).mul_mem hz hw
  · apply Subfield.map_le_iff_le_comap.mpr
    apply IntermediateField.adjoin_le_subfield
    · rintro _ ⟨c, rfl⟩
      change algebraMap K L (c : K) ∈ pPowerSubfield L p
      obtain ⟨d, hd⟩ := (mem_pPowerSubfield K p (c : K)).mp c.property
      exact (mem_pPowerSubfield L p _).mpr ⟨algebraMap K L d, by rw [← map_pow, hd]⟩
    · rw [Set.singleton_subset_iff]
      exact (mem_pPowerSubfield L p _).mpr ⟨x, hpow⟩

/-- 拡大後のp乗部分体を含めた族は、底体内で係数aを添加した族の像。
次の帰納段階では左辺を部分体族として使う。 -/
theorem subfield_sup_pPower_primeRoot_eq_map_adjoin
    (E : Subfield K) (hE : pPowerSubfield K p ≤ E)
    (x : L) (a : K) (hpow : x ^ p = algebraMap K L a)
    (hs : Algebra.adjoin K {x} = ⊤) :
    E.map (algebraMap K L) ⊔ pPowerSubfield L p =
      (IntermediateField.adjoin E {a}).toSubfield.map (algebraMap K L) := by
  rw [pPowerSubfield_primeRoot_eq_map_adjoin x a hpow hs, ← Subfield.map_sup]
  congr 1
  apply le_antisymm
  · apply sup_le
    · intro c hc
      exact (IntermediateField.adjoin E {a}).algebraMap_mem ⟨c, hc⟩
    · apply IntermediateField.adjoin_le_subfield
      · rintro _ ⟨c, rfl⟩
        exact (IntermediateField.adjoin E {a}).algebraMap_mem ⟨c, hE c.property⟩
      · rw [Set.singleton_subset_iff]
        exact IntermediateField.mem_adjoin_simple_self E a
  · apply IntermediateField.adjoin_le_subfield
    · rintro _ ⟨c, rfl⟩
      exact (show E ≤ E ⊔ (IntermediateField.adjoin (pPowerSubfield K p) {a}).toSubfield
          from le_sup_left) c.property
    · rw [Set.singleton_subset_iff]
      exact (show (IntermediateField.adjoin (pPowerSubfield K p) {a}).toSubfield ≤
          E ⊔ (IntermediateField.adjoin (pPowerSubfield K p) {a}).toSubfield from le_sup_right)
          (IntermediateField.mem_adjoin_simple_self (pPowerSubfield K p) a)

/-- 次数pの非自明な添加後の族の交わりは、拡大後のp乗部分体。
各族は底体内でaを添加してからLへ写すことで与える。 -/
theorem iInf_subfieldFamily_primeRoot_eq_pPower
    (E : ι → Subfield K)
    (hdir : Directed (· ≥ ·) E)
    (hpowE : ∀ i, pPowerSubfield K p ≤ E i)
    (hinf : (⨅ i, E i) = pPowerSubfield K p)
    (x : L) (a : K) (hpow : x ^ p = algebraMap K L a)
    (hx : x ∉ Set.range (algebraMap K L)) (hs : Algebra.adjoin K {x} = ⊤) :
    (⨅ i, (IntermediateField.adjoin (E i) {a}).toSubfield.map (algebraMap K L)) =
      pPowerSubfield L p := by
  classical
  have ha : a ∉ pPowerSubfield K p := by
    intro h
    obtain ⟨c, hc⟩ := (mem_pPowerSubfield K p a).mp h
    exact primeRoot_coefficient_not_pow x a hpow hx c hc
  have hne : Nonempty ι := by
    by_contra h
    have hall : ∀ i : ι, a ∈ E i := fun i ↦ (h ⟨i⟩).elim
    exact ha (hinf ▸ Subfield.mem_iInf.mpr hall)
  let : Nonempty ι := hne
  rw [← Subfield.map_iInf, iInf_subfield_adjoin_primeRoot E hdir hpowE hinf a ha]
  exact (pPowerSubfield_primeRoot_eq_map_adjoin x a hpow hs).symm

/-- F_i(L^p)という拡大後の族の交わりは、非自明な次数pの添加ではL^p。 -/
theorem iInf_subfield_sup_pPower_primeRoot
    (E : ι → Subfield K)
    (hdir : Directed (· ≥ ·) E)
    (hpowE : ∀ i, pPowerSubfield K p ≤ E i)
    (hinf : (⨅ i, E i) = pPowerSubfield K p)
    (x : L) (a : K) (hpow : x ^ p = algebraMap K L a)
    (hx : x ∉ Set.range (algebraMap K L)) (hs : Algebra.adjoin K {x} = ⊤) :
    (⨅ i, (E i).map (algebraMap K L) ⊔ pPowerSubfield L p) = pPowerSubfield L p := by
  simp_rw [subfield_sup_pPower_primeRoot_eq_map_adjoin _ (hpowE _) x a hpow hs]
  exact iInf_subfieldFamily_primeRoot_eq_pPower E hdir hpowE hinf x a hpow hx hs

end PowerSubfield

end SerrePositivity
