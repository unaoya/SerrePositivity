module

public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Basic
public import SerrePositivity.CommutativeAlgebra.SystemOfParameters.Existence
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Logic.Equiv.Basic

/-! # 生成するイデアルを保つパラメータの取り替え

## 概要

- 素イデアル回避の拡張：有限生成イデアル `J ⊄ I` から、`m J + I` と有限個の素イデアルを避ける元が
  とれる（`exists_mem_ideal_avoiding_primes_and_maximalIdeal_mul_sup`、Stacks 00DS 型）。
  生成元の一つを単元係数の和で置き換えても生成イデアルは変わらない
  （`span_range_update_of_unit_coefficient`）。
- 生成するイデアルを保ったまま、次元を一つずつ下げる生成元を先頭へ集められる
  （`exists_cons_dimension_drop`、`exists_same_span_prefix_primary`）。パラメータ系の最後を
  指定した正則元にできる（`exists_same_span_with_regular_last`）。
- パラメータ系の最後の元を正の冪にしてもパラメータ系で（`IsSystemOfParameters.pow_last`）、
  生成イデアルを保ちながら最後の元の冪を指定の元に入れられる
  （`exists_same_span_parameters_with_last_pow_mem`）。

## 方針

極小素イデアルの回避による次元降下と、単元係数による生成元の置換を組み合わせ、生成するイデアルを
厳密に保つ。Noether 局所環での議論で、Cohen–Macaulay 性や剰余体の無限性は使わない。

## 規約

列は `Fin` の関数で表し、先頭の追加は `Fin.cons`、末尾は `Fin.snoc`。

## 使われ方

CLMST の段のパラメータの取り替え（`CLMST/StageParameterChange` など）と、最後の元の冪の
重複度（`ParameterLastPowerMultiplicity`）。Mathlib への提出候補（mathlib-upstream の G10）。
-/

@[expose] public noncomputable section

universe u v w

open IsLocalRing PrimeSpectrum RingTheory.Sequence

namespace SerrePositivity

section Perturbation

/-- 単元係数をもつ線形結合で一つの生成元を置き換えると、生成イデアルは保存される。 -/
theorem span_range_update_of_unit_coefficient
    {R : Type u} [CommRing R] {ι : Type v} [Fintype ι] [DecidableEq ι]
    (y c : ι → R) (i : ι) (hc : IsUnit (c i)) :
    Ideal.span (Set.range (Function.update y i (∑ j, c j * y j))) =
      Ideal.span (Set.range y) := by
  classical
  let J := Ideal.span (Set.range (Function.update y i (∑ j, c j * y j)))
  have hy : ∀ j, j ≠ i → y j ∈ J := by
    intro j hj
    exact Ideal.subset_span ⟨j, Function.update_of_ne hj _ _⟩
  have hb : ∑ j ∈ Finset.univ.erase i, c j * y j ∈ J := by
    apply J.sum_mem
    intro j hj
    exact J.mul_mem_left (c j) (hy j (Finset.mem_erase.mp hj).1)
  have hxi : c i * y i ∈ J := by
    have hx : ∑ j, c j * y j ∈ J := Ideal.subset_span ⟨i, Function.update_self _ _ _⟩
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)] at hx
    simpa using J.sub_mem hx hb
  have hyi : y i ∈ J := by
    obtain ⟨u, hu⟩ := hc
    rw [← hu] at hxi
    simpa [mul_assoc] using J.mul_mem_left (↑(u⁻¹) : R) hxi
  refine le_antisymm ?_ ?_
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    by_cases hj : j = i
    · subst j
      rw [Function.update_self]
      exact (Ideal.span (Set.range y)).sum_mem fun k _ ↦
        (Ideal.span (Set.range y)).mul_mem_left (c k)
          (Ideal.subset_span (Set.mem_range_self k))
    · rw [Function.update_of_ne hj]
      exact Ideal.subset_span (Set.mem_range_self j)
  · rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    by_cases hj : j = i
    · simpa [hj] using hyi
    · exact hy j hj

/-- 極大イデアル倍の外にある線形結合には、少なくとも一つ単元の係数がある。 -/
theorem exists_unit_coefficient_of_sum_notMem_maximalIdeal_mul
    {R : Type u} [CommRing R] [IsLocalRing R] {ι : Type v} [Fintype ι]
    (y c : ι → R)
    (hx : (∑ j, c j * y j) ∉
      IsLocalRing.maximalIdeal R * Ideal.span (Set.range y)) :
    ∃ i, IsUnit (c i) := by
  classical
  by_contra h
  simp only [not_exists] at h
  apply hx
  apply (IsLocalRing.maximalIdeal R * Ideal.span (Set.range y)).sum_mem
  intro j _
  exact Ideal.mul_mem_mul (by simpa [IsLocalRing.mem_maximalIdeal] using h j)
    (Ideal.subset_span (Set.mem_range_self j))

/-- 有限生成イデアル J が I に含まれなければ、`m J + I` にも含まれない。
素イデアル回避で単元係数を保証する例外イデアルに使う。 -/
theorem not_le_maximalIdeal_mul_sup_of_not_le
    {R : Type u} [CommRing R] [IsLocalRing R] (I J : Ideal R)
    (hJ : J.FG) (hJI : ¬ J ≤ I) :
    ¬ J ≤ IsLocalRing.maximalIdeal R * J ⊔ I := by
  intro h
  apply hJI
  apply Submodule.le_of_le_smul_of_le_jacobson_bot hJ
    (IsLocalRing.maximalIdeal_le_jacobson (⊥ : Ideal R))
  simpa only [smul_eq_mul, sup_comm] using h

/-- 素イデアルの有限集合と `m J + I` を同時に避ける J 内の元を選べる。
素イデアル回避は二つまで非素な例外を許し、Nakayama が例外への包含を排除する。 -/
theorem exists_mem_ideal_avoiding_primes_and_maximalIdeal_mul_sup
    {R : Type u} [CommRing R] [IsLocalRing R] (I J : Ideal R)
    (hJ : J.FG) (hJI : ¬ J ≤ I) (s : Finset (Ideal R))
    (hp : ∀ P ∈ s, P.IsPrime) (hJP : ∀ P ∈ s, ¬ J ≤ P) :
    ∃ x ∈ J, x ∉ IsLocalRing.maximalIdeal R * J ⊔ I ∧ ∀ P ∈ s, x ∉ P := by
  classical
  let B := IsLocalRing.maximalIdeal R * J ⊔ I
  have hJB : ¬ J ≤ B := not_le_maximalIdeal_mul_sup_of_not_le I J hJ hJI
  have havoid : ¬ ((J : Set R) ⊆ ⋃ P ∈ (↑(insert B s) : Set (Ideal R)), (P : Set R)) := by
    rw [Ideal.subset_union_prime B B (fun P hP hPB _ ↦ ?_)]
    · rintro ⟨P, hP, hle⟩
      rcases Finset.mem_insert.mp hP with rfl | hP
      · exact hJB hle
      · exact hJP P hP hle
    · exact hp P ((Finset.mem_insert.mp hP).resolve_left hPB)
  obtain ⟨x, hxJ, hx⟩ := Set.not_subset.mp havoid
  simp only [Set.mem_iUnion, not_exists] at hx
  exact ⟨x, hxJ, hx B (by simp), fun P hP ↦ hx P (by simp [hP])⟩

/-- 有限個の生成元の一つを置き換え、生成イデアルを保ったまま指定された
素イデアルと `m J + I` を避ける生成元を作れる。パラメータ変更の一段分の接続。 -/
theorem exists_update_generator_avoiding_primes
    {R : Type u} [CommRing R] [IsLocalRing R] {ι : Type v}
    [Finite ι] [DecidableEq ι] (I : Ideal R) (y : ι → R)
    (hJI : ¬ Ideal.span (Set.range y) ≤ I) (s : Finset (Ideal R))
    (hp : ∀ P ∈ s, P.IsPrime)
    (hJP : ∀ P ∈ s, ¬ Ideal.span (Set.range y) ≤ P) :
    ∃ (i : ι) (x : R),
      Ideal.span (Set.range (Function.update y i x)) = Ideal.span (Set.range y) ∧
      x ∉ IsLocalRing.maximalIdeal R * Ideal.span (Set.range y) ⊔ I ∧
      ∀ P ∈ s, x ∉ P := by
  let : Fintype ι := Fintype.ofFinite ι
  have hJ : (Ideal.span (Set.range y)).FG := by
    rw [← Ideal.submodule_span_eq]
    exact Submodule.fg_span (R := R) (Set.finite_range y)
  obtain ⟨x, hxJ, hxB, hxP⟩ :=
    exists_mem_ideal_avoiding_primes_and_maximalIdeal_mul_sup
      I (Ideal.span (Set.range y)) hJ hJI s hp hJP
  have hxspan : x ∈ Submodule.span R (Set.range y) := by
    simpa only [Ideal.submodule_span_eq] using hxJ
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp hxspan
  have hcsum : ∑ j, c j * y j = x := by simpa only [smul_eq_mul] using hc
  obtain ⟨i, hi⟩ := exists_unit_coefficient_of_sum_notMem_maximalIdeal_mul y c (by
    rw [hcsum]
    exact fun hmem ↦ hxB ((show
      IsLocalRing.maximalIdeal R * Ideal.span (Set.range y) ≤
        IsLocalRing.maximalIdeal R * Ideal.span (Set.range y) ⊔ I from le_sup_left) hmem))
  refine ⟨i, x, ?_, hxB, hxP⟩
  simpa only [hcsum] using span_range_update_of_unit_coefficient y c i hi

end Perturbation

section Sequence

variable {R : Type u} [CommRing R] [IsLocalRing R]

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
    exact (not_lt.mpr (ringKrullDim_quotient_le_zero_of_radical_eq_maximalIdeal I hI)) hpos
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

omit [CommRing R] [IsLocalRing R] [IsNoetherianRing R] in
/-- 列の先頭を追加する操作と、末尾を取り除く操作は両立する。 -/
private theorem init_cons {r : ℕ} (x : R) (z : Fin (r + 1) → R) :
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
    exact (radical_eq_maximalIdeal_iff_ringKrullDim_quotient_le_zero
      (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hIm)).mpr hdim
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
      · exact (radical_eq_maximalIdeal_iff_ringKrullDim_quotient_le_zero
      (ne_top_of_le_ne_top (maximalIdeal.isMaximal R).ne_top hIm)).mpr (not_lt.mp hpos)
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

end Sequence

section LastPower

open IsLocalRing
variable {R : Type u} [CommRing R]

/-- 列の最後だけを正の冪にしても、その生成イデアルの根基は変わらない。 -/
theorem radical_span_snoc_pow {r : ℕ} (y : Fin r → R) (a : R) (k : ℕ) (hk : 0 < k) :
    (Ideal.span (Set.range (Fin.snoc y (a ^ k)))).radical =
      (Ideal.span (Set.range (Fin.snoc y a))).radical := by
  simp only [Fin.range_snoc, Ideal.span_insert]
  rw [← Ideal.span_singleton_pow]
  calc
    _ = (((Ideal.span {a}) ^ k).radical ⊔ (Ideal.span (Set.range y)).radical).radical :=
      Ideal.radical_sup _ _
    _ = ((Ideal.span {a}).radical ⊔ (Ideal.span (Set.range y)).radical).radical := by
      rw [Ideal.radical_pow _ (Nat.ne_of_gt hk)]
    _ = _ := (Ideal.radical_sup _ _).symm

/-- 最後の生成元を正の冪にしたイデアルは、元の生成イデアルに含まれる。
パラメータ条件や局所性・Noether 性は不要。 -/
theorem span_snoc_pow_le {D : Type u} [CommRing D] {e : ℕ}
    (y : Fin e → D) (a : D) (k : ℕ) (hk : 0 < k) :
    Ideal.span (Set.range (Fin.snoc y (a ^ k))) ≤ Ideal.span (Set.range (Fin.snoc y a)) := by
  simp only [Fin.range_snoc, Ideal.span_insert]
  rw [← Ideal.span_singleton_pow]
  exact sup_le_sup (Ideal.pow_le_self (Nat.ne_of_gt hk)) le_rfl

/-- 列の最後を正の冪にする操作は、その生成イデアルを小さくする。 -/
theorem span_last_pow_le {D : Type u} [CommRing D] {e : ℕ}
    (z : Fin (e + 1) → D) (k : ℕ) (hk : 0 < k) :
    Ideal.span (Set.range (Fin.snoc (Fin.init z) (z (Fin.last e) ^ k))) ≤
      Ideal.span (Set.range z) := by
  simpa only [Fin.snoc_init_self] using span_snoc_pow_le (Fin.init z) (z (Fin.last e)) k hk

/-- パラメータ系の最後だけを正の冪にしてもパラメータ系となる。 -/
theorem IsSystemOfParameters.pow_last [IsLocalRing R] {r : ℕ} {y : Fin (r + 1) → R}
    (hy : IsSystemOfParameters R y) (k : ℕ) (hk : 0 < k) :
    IsSystemOfParameters R (Fin.snoc (Fin.init y) (y (Fin.last r) ^ k)) := by
  refine ⟨hy.1, ?_⟩
  rw [radical_span_snoc_pow _ _ k hk, Fin.snoc_init_self]
  exact hy.2

/-- 元の生成イデアルを保つ列の変更と、最後の元の正の冪の所属を同時に得る。 -/
theorem exists_same_span_parameters_with_last_pow_mem
    [IsLocalRing R] [IsNoetherianRing R] {r : ℕ}
    (y : Fin (r + 1) → R) (hy : IsSystemOfParameters R y)
    (g : R) (hgm : g ∈ maximalIdeal R) (hg : IsSMulRegular R g) :
    ∃ (y' : Fin (r + 1) → R) (k : ℕ),
      Ideal.span (Set.range y') = Ideal.span (Set.range y) ∧ 0 < k ∧
      IsSystemOfParameters R (Fin.snoc (Fin.init y') (y' (Fin.last r) ^ k)) ∧
      y' (Fin.last r) ^ k ∈ Ideal.span (Set.range (Fin.init y')) ⊔ Ideal.span {g} := by
  obtain ⟨y', hspan, hparam⟩ :=
    exists_same_span_with_regular_last y hy g hgm hg
  have hy' : IsSystemOfParameters R y' := ⟨hy.1, by rw [hspan]; exact hy.2⟩
  have hlast : y' (Fin.last r) ∈ maximalIdeal R := by
    rw [← hy'.2]
    exact Ideal.le_radical (Ideal.subset_span (Set.mem_range_self _))
  have hrad : (Ideal.span (Set.range (Fin.init y')) ⊔ Ideal.span {g}).radical = maximalIdeal R := by
    simpa only [Fin.range_snoc, Ideal.span_insert, sup_comm] using hparam.2
  obtain ⟨k, hk⟩ := Ideal.mem_radical_iff.mp (hrad.symm ▸ hlast)
  refine ⟨y', k + 1, hspan, by omega, hy'.pow_last (k + 1) (by omega), ?_⟩
  rw [pow_succ]
  exact (Ideal.span (Set.range (Fin.init y')) ⊔ Ideal.span {g}).mul_mem_right _ hk

end LastPower

end SerrePositivity
