module

public import SerrePositivity.PerfectComplex.ProjectiveBounds

/-! # Koszul 消滅から有限射影複体の振幅を確認する

環自身の高次 Koszul ホモロジーの長さが零なら、有限射影項をもつ複体に
Koszul 関手を適用しても、長さで測ったホモロジーの振幅は元の項の範囲に収まる。
これは反復錐の消滅定理に渡す (Kosₘ) の具体的な確認である。
-/

@[expose] public section

universe u

namespace SerrePositivity

open CategoryTheory CategoryTheory.Limits
open scoped ENNReal BigOperators

variable {R : Type u} [CommRing R] {J : Ideal R} (lam : NormalizedLength R J)
  (hfg : J.FG) {n : ℕ} (x : Fin n → R)
  (hJ : J ≤ (Ideal.span (Set.range x)).radical)

include hfg hJ in
/-- 有限射影項の振幅と環自身の Koszul 消滅から、係数つき Koszul の振幅を得る。
長さの有限性は仮定しない。 -/
theorem lambdaHomology_koszul_projective_amplitude
    (hzero : ∀ i : ℕ, 0 < i → lam.len (koszulHomologySelf x i) = 0)
    (P : CochainComplex (ModuleCat.{u} R) ℤ)
    (hfinite : ∀ q, Module.Finite R (P.X q))
    (hproj : ∀ q, Module.Projective R (P.X q))
    (a b : ℤ) (hbound : ∀ q, q < a ∨ b < q → IsZero (P.X q))
    (q : ℤ) (hq : q < a ∨ b < q) :
    lam.len ((koszulComplexOn x P).homology q) = 0 := by
  classical
  have hterm (i : ℤ) : ∃ r : ℕ, Nonempty (Retract (P.X i) (ModuleCat.of R (Fin r → R))) := by
    have := hfinite i
    have := hproj i
    exact finiteProjective_exists_retract _
  choose r hr using hterm
  have hle := lambdaHomology_koszulComplexOn_le_sum_of_retracts lam hfg x hJ
    a (b + 1 - a).toNat r P (fun i hi ↦ hbound i (by omega)) (fun i _ _ ↦ hr i) q
  have hsum : ∑ j ∈ Finset.range ((b + 1 - a).toNat),
      r (a + j) • lam.len ((koszulComplex x).homology (q - (a + j))) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    have hj' := Finset.mem_range.mp hj
    have hz : lam.len ((koszulComplex x).homology (q - (a + j))) = 0 := by
      rcases hq with hq | hq
      · have hn : q - (a + j) = -(((a + j - q).toNat : ℕ) : ℤ) := by omega
        rw [hn]
        exact hzero _ (by omega)
      · have hz := koszulComplex_isZero_homology_of_pos x (q - (a + j)) (by omega)
        have := ModuleCat.subsingleton_of_isZero hz
        exact lam.len_eq_zero_of_subsingleton _
    rw [hz, nsmul_zero]
  exact le_antisymm (hle.trans hsum.le) zero_le

end SerrePositivity
