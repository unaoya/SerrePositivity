module

public import SerrePositivity.LengthAlgebra.Cone
public import SerrePositivity.Asymptotic.NormalizedLimit

/-! # Koszul ホモロジーの二項公式と正規化極限

有界性は各次数の長さの `O(s)` にのみ要求する。複体自体は無限分解でもよい。
-/

@[expose] public section

universe u

namespace SerrePositivity.Asymptotic

open CategoryTheory Filter Asymptotics

variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)

/-- 各段の零ホモトピーと長さの有界性から、極限も同じ二項公式を満たす。 -/
theorem normalizedLimit_koszul_null_binomial {e : ℕ} (x : Fin e → R)
    (P : ℕ → CochainComplex (ModuleCat.{u} R) ℤ)
    (hx : ∀ n j, Nonempty (Homotopy (smulId (x j) (P n)) 0))
    (ht : ∀ n q, IsPowTorsion J ((P n).homology q))
    (hfin : ∀ n q, lam.len ((P n).homology q) ≠ ⊤)
    (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (s : ℕ → ℕ) (hs : ∀ n, 0 < s n)
    (hO : ∀ q, (fun n ↦ (lam.len ((P n).homology q)).toReal)
      =O[atTop] (fun n ↦ (s n : ℝ))) (q : ℤ) :
    normalizedLimit U s (fun n ↦ (lam.len ((koszulComplexOn x (P n)).homology q)).toReal) =
      ∑ j ∈ Finset.range (e + 1), (e.choose j : ℝ) *
        normalizedLimit U s (fun n ↦ (lam.len ((P n).homology (q + j))).toReal) := by
  simp_rw [lambdaHomology_koszul_null_binomial lam x _ (hx _) (ht _) (hfin _)]
  rw [normalizedLimit_sum U hU s hs _ _
    (fun (j : ℕ) _ ↦ (hO (q + j)).const_mul_left (e.choose j : ℝ))]
  apply Finset.sum_congr rfl
  intro j _
  exact normalizedLimit_const_mul U hU s hs _ (hO (q + j)) _

end SerrePositivity.Asymptotic
