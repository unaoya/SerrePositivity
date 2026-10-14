module

public import SerrePositivity.CLMST.CyclicPLength
public import SerrePositivity.CLMST.CyclicUnitLength
public import SerrePositivity.CommutativeAlgebra.PrincipalMaximalFactorization

/-! # pの因子を取り除く巡回長さの帰着

g=p^c g'の分解と、二つのperfectoidイデアルの包含は証明する。
差の長さ比較はCyclicTorsionComparisonで、証明済みのpねじれ商perfectoid性と
座標根による共通の長さ零判定へ接続する。ここには因子分解とイデアル包含だけを置く。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.CLMST
open IsLocalRing Section2 RootTowerLength

/-- 非零gからpの因子を有限回取り除ける。正則局所性やWitt表示は不要。 -/
theorem exists_p_power_factor_of_nonzero
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (p : ℕ) (hp : (p : A) ∈ maximalIdeal A) (g : A) (hg : g ≠ 0) :
    ∃ c : ℕ, ∃ g' : A, g = (p : A) ^ c * g' ∧ ¬ (p : A) ∣ g' :=
  exists_pow_mul_not_dvd (p : A) g hp hg

/-- 一元パラメータ系がpなら、非零元はpの冪と単元の積。 -/
theorem exists_p_power_unit_of_fin_one
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (t : Fin 1 → A) (p : ℕ)
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A))
    (g : A) (hg : g ≠ 0) :
    ∃ c : ℕ, ∃ g' : A, g = (p : A) ^ c * g' ∧ IsUnit g' := by
  have hp := span_parameter_fin_one t ht
  rw [htp] at hp
  exact exists_pow_mul_unit_of_principal_maximalIdeal (p : A) g hp hg

section Comparison
variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (g g' : A) (c : ℕ) (hg : g = (p : A) ^ c * g')

include c hg

omit [IsLocalRing A] [IsNoetherianRing A] in
/-- p因子を取り除くと、元のperfectoidイデアルは残りのイデアルに含まれる。 -/
theorem perfectoidIdeal_le_of_p_power_factor :
    perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g) ≤
      perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g') := by
  apply perfectoidIdeal_mono
  apply Ideal.span_singleton_le_span_singleton.mpr
  refine ⟨algebraMap A (CompletedTower A t p) ((p : A) ^ c), ?_⟩
  rw [hg, map_mul, mul_comm]

end Comparison
end SerrePositivity.CLMST
