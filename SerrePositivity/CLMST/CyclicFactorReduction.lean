module

public import SerrePositivity.LengthAlgebra.AlmostFactorQuotient
public import SerrePositivity.LengthAlgebra.CyclicPowerReduction
public import SerrePositivity.CLMST.CyclicPLength
public import SerrePositivity.CLMST.CyclicUnitLength
public import SerrePositivity.CommutativeAlgebra.PrincipalMaximalFactorization

/-! # pの因子を取り除く巡回長さの帰着

g=p^c g'の分解と、二つのperfectoidイデアルの包含は証明する。
差の核をp-almost zeroにする積の包含は明示的に受け、共通の長さ比較を適用する。
その積の包含をperfectoidの普遍性だけから得たとは扱わない。
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

/-- 一元パラメータ系でpを因子に持たない場合、単元の既知の巡回評価を使える。 -/
theorem completedLength_cyclic_fin_one_eq_zero_of_not_dvd
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (t : Fin 1 → A) (p : ℕ) [Fact p.Prime]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A))
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (g : A) (hpg : ¬ (p : A) ∣ g) (n : ℕ) :
    (completedNormalizedLength A t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len
      (CompletedTower A t p ⧸ ((completedTowerMaxIdeal A t p) ^ n ⊔
        perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g))) =
      0 := by
  have hp := span_parameter_fin_one t ht
  rw [htp] at hp
  exact completedLength_cyclic_unit_eq_zero A t p _ hperf g
    (isUnit_of_not_dvd_of_principal_maximalIdeal (p : A) g hp hpg) n

section Comparison
variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A)
    (i : Fin h) (hti : t i = (p : A))
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

include i hti in
/-- 差をp-almost zeroにする積の包含があれば、p因子の除去で一次巡回長さは変わらない。 -/
theorem completedLength_cyclic_first_eq_of_p_power_factor
    (hprod : perfectoidIdeal (CompletedTower A t p) p hperf (p : CompletedTower A t p) *
        perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g') ≤
      completedTowerMaxIdeal A t p ⊔
        perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g)) :
    (completedNormalizedLength A t p ht).len (CompletedTower A t p ⧸
      (completedTowerMaxIdeal A t p ⊔
        perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g))) =
    (completedNormalizedLength A t p ht).len (CompletedTower A t p ⧸
      (completedTowerMaxIdeal A t p ⊔
        perfectoidIdeal (CompletedTower A t p) p hperf
          (algebraMap A (CompletedTower A t p) g'))) := by
  have hb := LengthAlgebra.length_quotient_sup_eq_of_almost_factor
    (completedNormalizedLength A t p ht) (completedNormalizedLength_hasSup A t p ht)
    (perfectoidIdeal (CompletedTower A t p) p hperf (p : CompletedTower A t p)) _ _
    (perfectoidIdeal_le_of_p_power_factor A t p hperf g g' c hg) 1
    (by simpa only [pow_one] using hprod)
    (fun a ↦ completedLength_cyclic_p_eq_zero A t p ht i hti hperf a)
  have hI : (completedTowerMaxIdeal A t p) ^ 1 ⊔
      perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g) =
      completedTowerMaxIdeal A t p ⊔
      perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g) := by
    rw [pow_one]
  have hH : (completedTowerMaxIdeal A t p) ^ 1 ⊔
      perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g') =
      completedTowerMaxIdeal A t p ⊔
      perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g') := by
    rw [pow_one]
  rw [← (completedNormalizedLength A t p ht).len_congr _ _
    (Ideal.quotientEquivAlgOfEq (CompletedTower A t p) hI).toLinearEquiv,
    ← (completedNormalizedLength A t p ht).len_congr _ _
    (Ideal.quotientEquivAlgOfEq (CompletedTower A t p) hH).toLinearEquiv]
  exact hb

include i hti in
/-- p因子を取り除いた一次評価と差のalmost零性から、元の全ての冪の巡回評価を得る。 -/
theorem completedLength_cyclic_pow_eq_zero_of_p_power_factor
    (hprod : perfectoidIdeal (CompletedTower A t p) p hperf (p : CompletedTower A t p) *
        perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g') ≤
      completedTowerMaxIdeal A t p ⊔
        perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g))
    (hzero : (completedNormalizedLength A t p ht).len (CompletedTower A t p ⧸
      (completedTowerMaxIdeal A t p ⊔
        perfectoidIdeal (CompletedTower A t p) p hperf
          (algebraMap A (CompletedTower A t p) g'))) = 0)
    (n : ℕ) :
    (completedNormalizedLength A t p ht).len (CompletedTower A t p ⧸
      ((completedTowerMaxIdeal A t p) ^ n ⊔
        perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g))) =
      0 := by
  apply LengthAlgebra.cyclic_quotient_pow_length_eq_zero_of_first
    (completedNormalizedLength A t p ht)
  · exact (maximalIdeal A).fg_of_isNoetherianRing.map _
  · exact (completedLength_cyclic_first_eq_of_p_power_factor
      A t p ht i hti hperf g g' c hg hprod).trans hzero

end Comparison
end SerrePositivity.CLMST
