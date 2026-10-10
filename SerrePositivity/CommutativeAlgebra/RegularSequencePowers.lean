module

public import SerrePositivity.CommutativeAlgebra.KoszulResolution
public import Mathlib.RingTheory.Regular.RegularSequence

/-! # 正則列の正の冪

Noether 加群上の極大イデアル内の弱正則列は、各元を正の冪にしても弱正則である。
局所環での正則列の置換と、一つの正則なスカラーの冪から証明する。
-/

public section

namespace SerrePositivity

open RingTheory.Sequence

variable {R : Type*} [CommRing R] [IsLocalRing R]

/-- 先頭の元だけを正の冪に置き換える。 -/
theorem isWeaklyRegular_pow_cons
    (M : Type*) [AddCommGroup M] [Module R M] [IsNoetherian R M]
    {r : R} {rs : List R} (h : IsWeaklyRegular M (r :: rs))
    (hm : ∀ x ∈ r :: rs, x ∈ IsLocalRing.maximalIdeal R) (v : ℕ) (hv : 0 < v) :
    IsWeaklyRegular M (r ^ v :: rs) := by
  have hp : (r :: rs).Perm (rs ++ [r]) := by
    simpa using (List.perm_append_comm (l₁ := [r]) (l₂ := rs))
  have hh := IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal h hp hm
  rw [isWeaklyRegular_append_iff, isWeaklyRegular_singleton_iff] at hh
  have hh' : IsWeaklyRegular M (rs ++ [r ^ v]) := by
    rw [isWeaklyRegular_append_iff, isWeaklyRegular_singleton_iff]
    exact ⟨hh.1, IsSMulRegular.pow v hh.2⟩
  apply IsLocalRing.isWeaklyRegular_of_perm_of_subset_maximalIdeal hh'
    (by simp)
  intro x hx
  rcases List.mem_append.mp hx with hx | hx
  · exact hm x (List.mem_cons_of_mem r hx)
  · have hx' : x = r ^ v := List.mem_singleton.mp hx
    subst x
    exact (IsLocalRing.maximalIdeal R).pow_mem_of_mem (hm r (by simp)) v hv

/-- 極大イデアル内の弱正則列の全ての元を同じ正の冪に置き換える。 -/
theorem isWeaklyRegular_map_pow
    (M : Type*) [AddCommGroup M] [Module R M] [IsNoetherian R M]
    {rs : List R} (h : IsWeaklyRegular M rs)
    (hm : ∀ x ∈ rs, x ∈ IsLocalRing.maximalIdeal R) (v : ℕ) (hv : 0 < v) :
    IsWeaklyRegular M (rs.map (fun x ↦ x ^ v)) := by
  induction rs generalizing M with
  | nil => exact .nil R M
  | cons r rs ih =>
    have hh := isWeaklyRegular_pow_cons M h hm v hv
    rw [isWeaklyRegular_cons_iff] at hh
    exact .cons hh.1 (ih _ hh.2 (fun x hx ↦ hm x (List.mem_cons_of_mem r hx)))

/-- 極大イデアルを生成する弱正則列の各正の冪も Koszul 分解を与える。 -/
theorem isKoszulResolution_powers_of_isWeaklyRegular [IsNoetherianRing R]
    {e : ℕ} (z : Fin e → R)
    (hz : Ideal.span (Set.range z) = IsLocalRing.maximalIdeal R)
    (hreg : IsWeaklyRegular R (List.ofFn z)) (v : ℕ) (hv : 0 < v) :
    IsKoszulResolution (fun j ↦ z j ^ v) := by
  apply isKoszulResolution_of_isWeaklyRegular
  have hm : ∀ x ∈ List.ofFn z, x ∈ IsLocalRing.maximalIdeal R := by
    intro x hx
    rw [← hz]
    exact Ideal.subset_span (by simpa only [List.mem_ofFn, Set.mem_range] using hx)
  simpa only [List.map_ofFn, Function.comp_def] using
    isWeaklyRegular_map_pow R hreg hm v hv

end SerrePositivity
