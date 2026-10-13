module

public import SerrePositivity.CommutativeAlgebra.ParameterGeneratorPerturbation
public import SerrePositivity.CommutativeAlgebra.ParameterAvoidance
public import SerrePositivity.CommutativeAlgebra.Multiplicity
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Logic.Equiv.Basic

/-! # 生成イデアルを保つパラメータ列の選択

残りの生成元を単元係数で置き換え、その元を先頭へ移す。
極小素イデアルの回避による次元降下と生成イデアルの厳密な保存を同時に行う。
Noether 局所環での議論であり、Cohen–Macaulay 性や剰余体の無限性は使わない。
-/

@[expose] public noncomputable section
universe u
open IsLocalRing PrimeSpectrum
namespace SerrePositivity
namespace ParameterGeneratorSequence

variable {R : Type u} [CommRing R] [IsLocalRing R]

/-- 極大イデアルを根基とするイデアルの商は零次元以下。 -/
theorem quotient_dim_le_zero_of_radical_eq_maximalIdeal (I : Ideal R)
    (hI : I.radical = maximalIdeal R) : ringKrullDim (R ⧸ I) ≤ 0 := by
  rw [ringKrullDim_quotient]
  refine Order.krullDim_nonpos_iff_forall_isMax.mpr fun q q' _ ↦ ?_
  have hm : maximalIdeal R ≤ q.1.asIdeal := by
    rw [← hI, ← q.1.isPrime.radical]
    exact Ideal.radical_mono q.2
  exact (le_maximalIdeal q'.1.isPrime.ne_top).trans hm

/-- 根基が極大イデアルである左因子に、極大イデアル内のイデアルを加えても根基は変わらない。 -/
theorem radical_sup_eq_maximalIdeal (I J : Ideal R)
    (hI : I.radical = maximalIdeal R) (hJ : J ≤ maximalIdeal R) :
    (I ⊔ J).radical = maximalIdeal R := by
  refine le_antisymm ?_ ?_
  · exact (maximalIdeal.isMaximal R).isPrime.radical_le_iff.mpr
      (sup_le (hI ▸ I.le_radical) hJ)
  · rw [← hI]
    exact Ideal.radical_mono le_sup_left

variable [IsNoetherianRing R]

/-- 正次元の商に対し、残りの生成イデアルを厳密に保ち、その先頭の元で次元を一つ下げる。
極小素イデアル回避、単元係数による置換、先頭との交換を組み合わせる。 -/
theorem exists_cons_dimension_drop (I : Ideal R) {r : ℕ} (y : Fin (r + 1) → R)
    (hprimary : (I ⊔ Ideal.span (Set.range y)).radical = maximalIdeal R)
    (hpos : 0 < ringKrullDim (R ⧸ I)) :
    ∃ (x : R) (z : Fin r → R),
      Ideal.span (Set.range (Fin.cons x z)) = Ideal.span (Set.range y) ∧
      x ∈ maximalIdeal R ∧
      ringKrullDim (R ⧸ (I ⊔ Ideal.span {x})) + 1 = ringKrullDim (R ⧸ I) := by
  classical
  let J := Ideal.span (Set.range y)
  let s := I.finite_minimalPrimes_of_isNoetherianRing.toFinset
  have hJI : ¬ J ≤ I := by
    intro h
    change Ideal.span (Set.range y) ≤ I at h
    have hI : I.radical = maximalIdeal R := by
      simpa only [sup_of_le_left h] using hprimary
    exact (not_lt.mpr (quotient_dim_le_zero_of_radical_eq_maximalIdeal I hI)) hpos
  have hJP : ∀ P ∈ s, ¬ J ≤ P := by
    intro P hP hJP
    have hmin : P ∈ I.minimalPrimes := by simpa [s] using hP
    have hmP : maximalIdeal R ≤ P := by
      rw [← hprimary, ← hmin.1.1.radical]
      exact Ideal.radical_mono (sup_le hmin.1.2 hJP)
    have hzero : ringKrullDim (R ⧸ I) ≤ 0 := by
      rw [ringKrullDim_quotient]
      refine Order.krullDim_nonpos_iff_forall_isMax.mpr fun q q' _ ↦ ?_
      have hPq : P ≤ q.1.asIdeal :=
        hmin.2 ⟨q.1.isPrime, q.2⟩ ((le_maximalIdeal q.1.isPrime.ne_top).trans hmP)
      exact (le_maximalIdeal q'.1.isPrime.ne_top).trans (hmP.trans hPq)
    exact (not_lt.mpr hzero) hpos
  obtain ⟨i, x, hspan, _, hx⟩ := exists_update_generator_avoiding_primes I y hJI s
    (fun P hP ↦ (show P ∈ I.minimalPrimes by simpa [s] using hP).1.1) hJP
  have hxJ : x ∈ J := by
    change x ∈ Ideal.span (Set.range y)
    rw [← hspan]
    exact Ideal.subset_span ⟨i, Function.update_self _ _ _⟩
  have hxm : x ∈ maximalIdeal R :=
    hprimary ▸ (I ⊔ J).le_radical ((show J ≤ I ⊔ J from le_sup_right) hxJ)
  have hdim := Module.supportDim_quotSMulTop_succ_eq_of_notMem_minimalPrimes_of_mem_maximalIdeal
    (M := R ⧸ I) (by
      rw [Ideal.annihilator_quotient]
      intro P hP
      exact hx P (by simpa [s] using hP)) hxm
  rw [supportDim_quotSMulTop_quotient, Module.supportDim_quotient_eq_ringKrullDim] at hdim
  let y' := Function.update y i x ∘ Equiv.swap (0 : Fin (r + 1)) i
  have hrange : Set.range y' = Set.range (Function.update y i x) := by
    ext a
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨Equiv.swap 0 i j, rfl⟩
    · rintro ⟨j, rfl⟩
      exact ⟨Equiv.swap 0 i j, by simp [y', Function.comp_apply]⟩
  have hzero : y' 0 = x := by simp [y', Function.comp_apply]
  refine ⟨x, Fin.tail y', ?_, hxm, hdim⟩
  rw [← hzero, Fin.cons_self_tail, hrange, hspan]

omit [IsNoetherianRing R] in
/-- 極大イデアル内のイデアルの商が零次元以下なら、そのイデアルは極大イデアル準素。 -/
theorem radical_eq_maximalIdeal_of_quotient_dim_le_zero (I : Ideal R)
    (hIm : I ≤ maximalIdeal R) (hdim : ringKrullDim (R ⧸ I) ≤ 0) :
    I.radical = maximalIdeal R := by
  have hItop : I ≠ ⊤ := by
    intro h
    exact (maximalIdeal.isMaximal R).ne_top
      (top_le_iff.mp (h ▸ hIm))
  let : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hItop
  exact radical_eq_maximalIdeal_of_ringKrullDim_quotient
    (le_antisymm hdim ringKrullDim_nonneg_of_nontrivial)

omit [CommRing R] [IsLocalRing R] [IsNoetherianRing R] in
/-- 列の先頭を追加する操作と、末尾を取り除く操作は両立する。 -/
theorem init_cons {r : ℕ} (x : R) (z : Fin (r + 1) → R) :
    Fin.init (Fin.cons x z : Fin (r + 2) → R) =
      (Fin.cons x (Fin.init z) : Fin (r + 1) → R) := by
  ext i
  cases i using Fin.cases <;> rfl

/-- 商の次元が r 以下で、残りの生成元が r+1 本なら、生成イデアルを保ちつつ
先頭 r 本と既存のイデアル I が極大イデアル準素になるように列を変更できる。
次元が先に零になった場合は、残りの生成元を変更せずに保つ。 -/
theorem exists_same_span_prefix_primary (I : Ideal R) (r : ℕ) (y : Fin (r + 1) → R)
    (hIm : I ≤ maximalIdeal R)
    (hprimary : (I ⊔ Ideal.span (Set.range y)).radical = maximalIdeal R)
    (hdim : ringKrullDim (R ⧸ I) ≤ r) :
    ∃ y' : Fin (r + 1) → R,
      Ideal.span (Set.range y') = Ideal.span (Set.range y) ∧
      (I ⊔ Ideal.span (Set.range (Fin.init y'))).radical = maximalIdeal R := by
  classical
  induction r generalizing I with
  | zero =>
    refine ⟨y, rfl, ?_⟩
    have he : Set.range (Fin.init y) = ∅ := by simp
    rw [he, Ideal.span_empty, sup_bot_eq]
    exact radical_eq_maximalIdeal_of_quotient_dim_le_zero I hIm hdim
  | succ r ih =>
    by_cases hpos : 0 < ringKrullDim (R ⧸ I)
    · obtain ⟨x, z, hspan, hxm, hdrop⟩ := exists_cons_dimension_drop I y hprimary hpos
      have hdim' : ringKrullDim (R ⧸ (I ⊔ Ideal.span {x})) ≤ r := by
        apply ENat.WithBot.add_le_add_one_right_iff.mp
        simpa only [hdrop, Nat.cast_succ] using hdim
      have hIm' : I ⊔ Ideal.span {x} ≤ maximalIdeal R :=
        sup_le hIm ((maximalIdeal R).span_singleton_le_iff_mem.mpr hxm)
      have hprimary' : ((I ⊔ Ideal.span {x}) ⊔ Ideal.span (Set.range z)).radical =
          maximalIdeal R := by
        rw [sup_assoc, ← Ideal.span_insert, ← Fin.range_cons, hspan]
        exact hprimary
      obtain ⟨z', hzspan, hzprimary⟩ := ih (I ⊔ Ideal.span {x}) z hIm' hprimary' hdim'
      refine ⟨Fin.cons x z', ?_, ?_⟩
      · rw [Fin.range_cons, Ideal.span_insert, hzspan, ← Ideal.span_insert,
          ← Fin.range_cons, hspan]
      · rw [init_cons, Fin.range_cons, Ideal.span_insert, ← sup_assoc]
        exact hzprimary
    · refine ⟨y, rfl, ?_⟩
      apply radical_sup_eq_maximalIdeal I
      · exact radical_eq_maximalIdeal_of_quotient_dim_le_zero I hIm (not_lt.mp hpos)
      · have hym : Ideal.span (Set.range y) ≤ maximalIdeal R :=
          le_sup_right.trans (hprimary ▸ (I ⊔ Ideal.span (Set.range y)).le_radical)
        apply le_trans ?_ hym
        apply Ideal.span_mono
        rintro a ⟨i, rfl⟩
        exact ⟨i.castSucc, rfl⟩

/-- 非単元の正則元 g を最後に置くパラメータ系を、元の生成イデアルを保った
変更列の先頭部分から作れる。次元 r+1 の列を用い、商の次元上界は非零因子から導く。 -/
theorem exists_same_span_with_regular_last {r : ℕ} (y : Fin (r + 1) → R)
    (hy : IsSystemOfParameters R y) (g : R) (hgm : g ∈ maximalIdeal R)
    (hg : IsSMulRegular R g) :
    ∃ y' : Fin (r + 1) → R,
      Ideal.span (Set.range y') = Ideal.span (Set.range y) ∧
      IsSystemOfParameters R (Fin.snoc (Fin.init y') g) := by
  have hgIdeal : Ideal.span {g} ≤ maximalIdeal R :=
    (maximalIdeal R).span_singleton_le_iff_mem.mpr hgm
  have hprimary : (Ideal.span {g} ⊔ Ideal.span (Set.range y)).radical =
      maximalIdeal R := by
    rw [sup_comm]
    exact radical_sup_eq_maximalIdeal _ _ hy.2 hgIdeal
  have hgdiv : g ∈ nonZeroDivisors R := by
    apply mem_nonZeroDivisors_iff_left.mpr
    intro x hx
    exact hg.right_eq_zero_of_smul hx
  have hdim : ringKrullDim (R ⧸ Ideal.span {g}) ≤ r := by
    apply ENat.WithBot.add_le_add_one_right_iff.mp
    have h := ringKrullDim_quotient_succ_le_of_nonZeroDivisor hgdiv
    rw [hy.1] at h
    simpa only [Nat.cast_succ] using h
  obtain ⟨y', hspan, hrad⟩ :=
    exists_same_span_prefix_primary (Ideal.span {g}) r y hgIdeal hprimary hdim
  refine ⟨y', hspan, hy.1, ?_⟩
  rw [Fin.range_snoc, Ideal.span_insert]
  exact hrad

end ParameterGeneratorSequence
end SerrePositivity
