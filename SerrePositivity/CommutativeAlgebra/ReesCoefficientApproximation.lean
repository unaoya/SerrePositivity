module

public import SerrePositivity.CommutativeAlgebra.ReesIdealLifts
public import SerrePositivity.CommutativeAlgebra.Adic.Finite

/-! # 有限なRees生成元から次数を制御した近似へ -/

@[expose] public section
universe u
namespace SerrePositivity.HilbertSamuel
open scoped BigOperators
variable {R : Type u} [CommRing R]

/-- 次数がc以下の多項式との積の係数を、固定された有限添字で展開する。 -/
theorem polynomial_coeff_mul_fin (p q : Polynomial R) (c n : ℕ) (hq : q.natDegree ≤ c) :
    (p * q).coeff n = ∑ d : Fin (c + 1),
      (if d.val ≤ n then p.coeff (n - d.val) else 0) * q.coeff d.val := by
  have he : q = ∑ d : Fin (c + 1), Polynomial.monomial d.val (q.coeff d.val) := by
    exact (q.as_sum_range' (c + 1) (by omega)).trans
      (Fin.sum_univ_eq_sum_range (fun d ↦ Polynomial.monomial d (q.coeff d)) (c + 1)).symm
  calc
    (p * q).coeff n = (p * ∑ d : Fin (c + 1),
      Polynomial.monomial d.val (q.coeff d.val)).coeff n := congrArg (fun t ↦ (p * t).coeff n) he
    _ = ∑ d : Fin (c + 1), (p * Polynomial.monomial d.val (q.coeff d.val)).coeff n := by
      simp only [Finset.mul_sum, Polynomial.finsetSum_coeff]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [← Polynomial.C_mul_X_pow_eq_monomial, ← mul_assoc, Polynomial.coeff_mul_X_pow']
      split_ifs <;> simp only [Polynomial.coeff_mul_C, zero_mul]

/-- 有限直積で、各係数がIに属するならベクトルはI倍部分加群に入る。 -/
theorem mem_smul_top_pi_of_mem {κ : Type*} [Finite κ] (I : Ideal R) (v : κ → R)
    (hv : ∀ j, v j ∈ I) : v ∈ I • (⊤ : Submodule R (κ → R)) := by
  classical
  let : Fintype κ := Fintype.ofFinite κ
  have he : (∑ j, v j • Pi.single j (1 : R)) = v := (pi_eq_sum_univ' v).symm
  rw [← he]
  exact Submodule.sum_mem _ (fun j _ ↦ Submodule.smul_mem_smul (hv j) (Submodule.mem_top))

/-- 随伴次数環での有限な生成元から、元のイデアルへの一様な次数付き近似を作る。
完備性・Noether性は仮定せず、近似の極限への移行と分離する。 -/
theorem exists_shifted_approximation_of_rees_lifts (I J : Ideal R)
    {r : ℕ} (z : Fin r → reesAlgebra I)
    (hz : ∀ i k, (z i : Polynomial R).coeff k ∈ J)
    (hspan : Ideal.span (Set.range (fun i ↦ Ideal.Quotient.mk
      (I.map (algebraMap R (reesAlgebra I))) (z i))) =
      (reesCoefficientIdeal R I J).map
        (Ideal.Quotient.mk (I.map (algebraMap R (reesAlgebra I))))) :
    ∃ c : ℕ, ∃ f : (Fin r × Fin (c + 1) → R) →ₗ[R] R,
      f.range ≤ J ∧ ∀ n x, x ∈ J → x ∈ I ^ n →
        ∃ v, v ∈ I ^ (n - c) • (⊤ : Submodule R (Fin r × Fin (c + 1) → R)) ∧
          x - f v ∈ I ^ (n + 1) := by
  classical
  let c := Finset.univ.sup (fun i ↦ (z i : Polynomial R).natDegree)
  have hc (i : Fin r) : (z i : Polynomial R).natDegree ≤ c := by
    exact Finset.le_sup (f := fun i ↦ (z i : Polynomial R).natDegree) (Finset.mem_univ i)
  let f := Fintype.linearCombination R (fun a : Fin r × Fin (c + 1) ↦
    (z a.1 : Polynomial R).coeff a.2.val)
  refine ⟨c, f, ?_, ?_⟩
  · rintro _ ⟨v, rfl⟩
    exact J.sum_mem (fun a _ ↦ J.mul_mem_left (v a) (hz a.1 a.2.val))
  · intro n x hxJ hxI
    let G := GradedReesRing R I
    let q := Ideal.Quotient.mk (I.map (algebraMap R (reesAlgebra I)))
    let m : reesAlgebra I := ⟨Polynomial.monomial n x, reesAlgebra.monomial_mem.mpr hxI⟩
    have hm : q m ∈ Ideal.span (Set.range (fun i ↦ q (z i))) := by
      rw [hspan]
      exact Ideal.mem_map_of_mem q (monomial_mem_reesCoefficientIdeal R I J n x hxI hxJ)
    have hm' : q m ∈ (Fintype.linearCombination G (fun i ↦ q (z i))).range := by
      rw [Fintype.range_linearCombination]
      exact hm
    obtain ⟨a, ha⟩ := hm'
    choose b hb using fun i : Fin r ↦ Ideal.Quotient.mk_surjective (a i)
    have hb' : ∀ i, q (b i) = a i := hb
    have ha' : (∑ i, a i * q (z i)) = q m := by
      simpa only [Fintype.linearCombination_apply, smul_eq_mul] using ha
    have hzero : q (m - ∑ i, b i * z i) = 0 := by
      rw [map_sub, map_sum]
      simp only [map_mul, hb']
      exact sub_eq_zero.mpr ha'.symm
    have herr := (mem_map_algebraMap_reesAlgebra_iff (I := I) (m - ∑ i, b i * z i)).mp
      (Ideal.Quotient.eq_zero_iff_mem.mp hzero) n
    let v : Fin r × Fin (c + 1) → R := fun a ↦
      if a.2.val ≤ n then (b a.1 : Polynomial R).coeff (n - a.2.val) else 0
    refine ⟨v, mem_smul_top_pi_of_mem (I ^ (n - c)) v ?_, ?_⟩
    · intro a
      dsimp only [v]
      split_ifs with h
      · have hd : a.2.val ≤ c := Nat.le_of_lt_succ a.2.isLt
        exact Ideal.pow_le_pow_right (by omega : n - c ≤ n - a.2.val)
          ((mem_reesAlgebra_iff I _).mp (b a.1).property (n - a.2.val))
      · exact Ideal.zero_mem _
    · have he : f v = (∑ i, (b i : Polynomial R) * (z i : Polynomial R)).coeff n := by
        simp only [f, Fintype.linearCombination_apply, smul_eq_mul, Fintype.sum_prod_type,
          Polynomial.finsetSum_coeff, polynomial_coeff_mul_fin _ _ c n (hc _), v]
      change ((reesAlgebra I).val (m - ∑ i, b i * z i)).coeff n ∈ I ^ (n + 1) at herr
      rw [map_sub, map_sum] at herr
      simp only [map_mul] at herr
      change (Polynomial.monomial n x - ∑ i, (b i : Polynomial R) * (z i : Polynomial R)).coeff n
        ∈ I ^ (n + 1) at herr
      simpa only [Polynomial.coeff_sub, Polynomial.coeff_monomial, ite_true, ← he] using herr

end SerrePositivity.HilbertSamuel
