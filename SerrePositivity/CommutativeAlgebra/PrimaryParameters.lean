module

public import SerrePositivity.CommutativeAlgebra.ParameterAvoidance
public import SerrePositivity.CommutativeAlgebra.FiniteLength

/-! # 準素イデアル内でのパラメータの選択

Noether 局所環の商の次元を、極小素イデアルを避ける元によって一つずつ下げる。
極大イデアルを根基とするイデアル `H` の中から、指定された個数の元を選んで
有限長の商を作る。正則性や Cohen–Macaulay 性は要求しない。

整域の非零元 `g` による商は次元が少なくとも一つ下がるので、
残りの `dim R - 1` 個を `H` の中で選べる。§2 の共通分母の誤差評価に使う。
-/

public section

open IsLocalRing PrimeSpectrum

namespace SerrePositivity

variable (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]

omit [IsLocalRing R] in
/-- 零次元以下の Noether 商環は、元の環上で有限長である。零環の場合も含む。 -/
theorem isFiniteLength_quotient_of_ringKrullDim_le_zero (I : Ideal R)
    (hdim : ringKrullDim (R ⧸ I) ≤ 0) : IsFiniteLength R (R ⧸ I) := by
  have : IsNoetherianRing (R ⧸ I) :=
    isNoetherianRing_of_surjective R _ (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
  have : IsArtinianRing (R ⧸ I) := by
    apply isArtinianRing_iff_krullDimLE_zero.mpr
    exact (Ring.krullDimLE_iff).mpr hdim
  exact isFiniteLength_of_le_radical_annihilator I (R ⧸ I) (by
    simpa only [Ideal.annihilator_quotient] using I.le_radical)

/-- 正次元の商に対し、極大イデアルを根基とする `H` の中で元を選ぶと次元を一つ下げられる。
`H` を含みうる極小素イデアルがないことと、有限素イデアル回避を使う。 -/
theorem exists_dimension_drop_in_primary (I H : Ideal R) (hH : H.radical = maximalIdeal R)
    (hpos : 0 < ringKrullDim (R ⧸ I)) :
    ∃ y ∈ H, ringKrullDim (R ⧸ (I ⊔ Ideal.span {y})) + 1 = ringKrullDim (R ⧸ I) := by
  classical
  let s := I.finite_minimalPrimes_of_isNoetherianRing.toFinset
  have hnot : ∀ p ∈ s, ¬ H ≤ p := by
    intro p hp hHp
    have hpm : p ∈ I.minimalPrimes := by simpa [s] using hp
    have hmp : maximalIdeal R ≤ p := by
      rw [← hH, ← hpm.1.1.radical]
      exact Ideal.radical_mono hHp
    have hzero : ringKrullDim (R ⧸ I) ≤ 0 := by
      rw [ringKrullDim_quotient]
      refine Order.krullDim_nonpos_iff_forall_isMax.mpr fun q q' hqq' ↦ ?_
      have hpq : p ≤ q.1.asIdeal :=
        hpm.2 ⟨q.1.isPrime, q.2⟩ ((le_maximalIdeal q.1.isPrime.ne_top).trans hmp)
      exact (le_maximalIdeal q'.1.isPrime.ne_top).trans (hmp.trans hpq)
    exact (not_lt.mpr hzero) hpos
  have hsub : ¬ ((H : Set R) ⊆ ⋃ p ∈ (↑s : Set (Ideal R)), (p : Set R)) := by
    rw [Ideal.subset_union_prime ⊥ ⊥ (fun p hp _ _ ↦ ?_)]
    · rintro ⟨p, hp, hHp⟩
      exact hnot p hp hHp
    · exact (show p ∈ I.minimalPrimes by simpa [s] using hp).1.1
  obtain ⟨y, hyH, hy⟩ := Set.not_subset.mp hsub
  simp only [Set.mem_iUnion, not_exists] at hy
  have hymin : ∀ p ∈ I.minimalPrimes, y ∉ p := by
    intro p hp
    exact hy p (by simpa [s] using hp)
  have hym : y ∈ maximalIdeal R := hH ▸ H.le_radical hyH
  have hdim := Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
    (M := R ⧸ I) (by rwa [Ideal.annihilator_quotient]) hym
  rw [supportDim_quotSMulTop_quotient, Module.supportDim_quotient_eq_ringKrullDim] at hdim
  exact ⟨y, hyH, hdim⟩

/-- `dim R/I ≤ r` なら、準素イデアル `H` の中の `r` 個の元で商を有限長にできる。
次元が先に零になった場合は残りを零で埋める。 -/
theorem exists_parameters_mod_ideal_in_primary (H : Ideal R) (hH : H.radical = maximalIdeal R)
    (r : ℕ) (I : Ideal R) (hdim : ringKrullDim (R ⧸ I) ≤ r) :
    ∃ z : Fin r → R, (∀ i, z i ∈ H) ∧
      IsFiniteLength R (R ⧸ (I ⊔ Ideal.span (Set.range z))) := by
  classical
  induction r generalizing I with
  | zero =>
      refine ⟨Fin.elim0, fun i ↦ Fin.elim0 i, ?_⟩
      have he : Set.range (Fin.elim0 : Fin 0 → R) = ∅ := by simp
      rw [he, Ideal.span_empty, sup_bot_eq]
      exact isFiniteLength_quotient_of_ringKrullDim_le_zero R I hdim
  | succ r ih =>
      by_cases hpos : 0 < ringKrullDim (R ⧸ I)
      · obtain ⟨y, hy, hd⟩ := exists_dimension_drop_in_primary R I H hH hpos
        have hd' : ringKrullDim (R ⧸ (I ⊔ Ideal.span {y})) ≤ r := by
          have hh : ringKrullDim (R ⧸ (I ⊔ Ideal.span {y})) + 1 ≤ (r : WithBot ℕ∞) + 1 := by
            simpa only [hd, Nat.cast_succ] using hdim
          exact ENat.WithBot.add_le_add_one_right_iff.mp hh
        obtain ⟨z, hz, hf⟩ := ih (I ⊔ Ideal.span {y}) hd'
        refine ⟨Fin.cons y z, ?_, ?_⟩
        · intro i
          refine Fin.cases hy (fun j ↦ ?_) i
          exact hz j
        · rw [Fin.range_cons, Ideal.span_insert, ← sup_assoc]
          exact hf
      · refine ⟨fun _ ↦ 0, fun _ ↦ H.zero_mem, ?_⟩
        have he : Ideal.span (Set.range (fun _ : Fin (r + 1) ↦ (0 : R))) = ⊥ := by simp
        rw [he, sup_bot_eq]
        exact isFiniteLength_quotient_of_ringKrullDim_le_zero R I (not_lt.mp hpos)

/-- 次元 `r+1` の局所整域の非零元 `g` に対して、`H` 内の `r` 個の元と合わせて有限長の商を作れる。
非零因子による次元降下と、準素イデアル内のパラメータ選択を組み合わせる。 -/
theorem exists_error_parameters_in_primary [IsDomain R]
    (H : Ideal R) (hH : H.radical = maximalIdeal R)
    (g : R) (hg : g ≠ 0) {r : ℕ} (hdim : ringKrullDim R = r + 1) :
    ∃ z : Fin r → R, (∀ i, z i ∈ H) ∧
      IsFiniteLength R (R ⧸ (Ideal.span {g} ⊔ Ideal.span (Set.range z))) := by
  apply exists_parameters_mod_ideal_in_primary R H hH r (Ideal.span {g})
  have hd := ringKrullDim_quotient_succ_le_of_nonZeroDivisor
    (mem_nonZeroDivisors_iff_ne_zero.mpr hg)
  rw [hdim] at hd
  exact ENat.WithBot.add_le_add_one_right_iff.mp hd

end SerrePositivity
