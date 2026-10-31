module

public import SerrePositivity.CLMST.PerfectoidIdealRoots
public import SerrePositivity.LengthAlgebra.RootTowerLength.Coordinate

/-! # 命題4.0.10の p の場合の数値接続

完備塔の p の全根が perfectoid ideal に属することを、選んだ商の被約性から確認し、
有限段の単項式の上界から巡回商の長さ零へ接続する。
被約性は標数pのperfectoid環がperfectであるという証明済みの結果から供給する。
g=pの場合を証明し、一般のgの命題4.0.10とは区別する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open Section2 IsLocalRing
variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ j, t j ∈ maximalIdeal A)

/-- pを座標に含む塔で、perfectoid商の被約性があればpの場合の巡回長さ評価を得る。 -/
theorem completedLength_cyclic_p_eq_zero_of_reduced
    (i : Fin h) (hti : t i = (p : A))
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (hred : IsReduced (perfectoidQuotient (CompletedTower A t p) p hperf
      (p : CompletedTower A t p))) (n : ℕ) :
    (RootTowerLength.completedNormalizedLength A t p ht).len
      (CompletedTower A t p ⧸ ((completedTowerMaxIdeal A t p) ^ n ⊔
        perfectoidIdeal (CompletedTower A t p) p hperf (p : CompletedTower A t p))) = 0 := by
  have hp : (p : A) ∈ maximalIdeal A := hti ▸ ht i
  have hIK : ((maximalIdeal A) ^ n).map (algebraMap A (CompletedTower A t p)) ≤
      (completedTowerMaxIdeal A t p) ^ n ⊔
        perfectoidIdeal (CompletedTower A t p) p hperf (p : CompletedTower A t p) := by
    rw [Ideal.map_pow]
    exact le_sup_left
  exact RootTowerLength.completedNormalizedLength_quotient_eq_zero_of_coordinate_roots
    A t p ht hp ((maximalIdeal A) ^ n)
    (RootTowerLength.finiteLength_quotient_maximalIdeal_pow A n) n le_rfl _ hIK i
    (fun m ↦ (le_sup_right : perfectoidIdeal (CompletedTower A t p) p hperf
      (p : CompletedTower A t p) ≤ _) (completedTowerRoot_mem_perfectoidIdeal_p_of_reduced
        A t p hperf hred m i hti))

/-- 標数pのperfectoid商の被約性を定義から供給し、pの場合の全巡回評価を得る。 -/
theorem completedLength_cyclic_p_eq_zero
    (i : Fin h) (hti : t i = (p : A))
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p) (n : ℕ) :
    (RootTowerLength.completedNormalizedLength A t p ht).len
      (CompletedTower A t p ⧸ ((completedTowerMaxIdeal A t p) ^ n ⊔
        perfectoidIdeal (CompletedTower A t p) p hperf (p : CompletedTower A t p))) = 0 :=
  completedLength_cyclic_p_eq_zero_of_reduced A t p ht i hti hperf
    (perfectoidQuotient_p_isReduced (CompletedTower A t p) p hperf) n

end SerrePositivity.CLMST
