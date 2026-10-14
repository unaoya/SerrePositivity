module

public import SerrePositivity.CommutativeAlgebra.PerfectoidIdealPowers
public import SerrePositivity.CLMST.CyclicFactorReduction

/-! # pの冪の単元倍と一元パラメータ系の巡回評価

pの正冪とpのperfectoidイデアルの一致を使い、g=p^c u（uは単元）の評価を証明する。
一元パラメータ系では全ての非零gがこの形なので、全射性や差のalmost零性の仮定を要しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open IsLocalRing Section2 RootTowerLength

/-- pの冪の単元倍の場合、任意の冪の巡回長さは零。 -/
theorem completedLength_cyclic_p_power_unit_eq_zero
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A) (i : Fin h) (hti : t i = (p : A))
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (g a : A) (c : ℕ) (hg : g = (p : A) ^ c * a) (ha : IsUnit a) (n : ℕ) :
    (completedNormalizedLength A t p ht).len (CompletedTower A t p ⧸
      ((completedTowerMaxIdeal A t p) ^ n ⊔
        perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g))) =
      0 := by
  by_cases hc : c = 0
  · subst c
    have hga : g = a := by simpa only [pow_zero, one_mul] using hg
    exact completedLength_cyclic_unit_eq_zero A t p ht hperf g (hga ▸ ha) n
  · have hI : perfectoidIdeal (CompletedTower A t p) p hperf
        (algebraMap A (CompletedTower A t p) g) =
        perfectoidIdeal (CompletedTower A t p) p hperf (p : CompletedTower A t p) := by
      rw [hg, map_mul, map_pow, map_natCast,
        perfectoidIdeal_mul_unit_eq _ p hperf _ _ (ha.map (algebraMap A (CompletedTower A t p))),
        perfectoidIdeal_p_pow_eq _ p hperf c (Nat.pos_of_ne_zero hc)]
    have heq := congrArg (fun I : Ideal (CompletedTower A t p) ↦
      (completedTowerMaxIdeal A t p) ^ n ⊔ I) hI
    exact ((completedNormalizedLength A t p ht).len_congr _ _
      (Ideal.quotientEquivAlgOfEq (CompletedTower A t p) heq).toLinearEquiv).trans
        (completedLength_cyclic_p_eq_zero A t p ht i hti hperf n)

/-- 一元パラメータ系では、全ての非零gに対して巡回長さ零が成立する。 -/
theorem completedLength_cyclic_fin_one_eq_zero
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    (t : Fin 1 → A) (p : ℕ) [Fact p.Prime]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A))
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (g : A) (hg : g ≠ 0) (n : ℕ) :
    (completedNormalizedLength A t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len
      (CompletedTower A t p ⧸ ((completedTowerMaxIdeal A t p) ^ n ⊔
        perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g))) =
      0 := by
  obtain ⟨c, a, hga, ha⟩ := exists_p_power_unit_of_fin_one A t p ht htp g hg
  exact completedLength_cyclic_p_power_unit_eq_zero A t p _ 0 htp hperf g a c hga ha n

end SerrePositivity.CLMST
