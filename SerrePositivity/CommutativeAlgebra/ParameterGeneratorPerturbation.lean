module

public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! # 生成イデアルを保つパラメータの変更の補助

単元係数をもつ線形結合で一つの生成元を置き換えても、生成イデアルは変わらない。
局所環では、極大イデアル倍を避ける線形結合に単元係数が存在する。
素イデアル回避に `m J + I` を例外として加えることで、既に選んだ列を保ちながら
そのような生成元を選べる。次元を下げる列全体の帰納的構成はここでは扱わない。
-/

@[expose] public section
universe u v
namespace SerrePositivity

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

end SerrePositivity
