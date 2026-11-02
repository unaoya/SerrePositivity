module

public import SerrePositivity.BhattScholze.PerfectoidIdeal.Basic
public import SerrePositivity.LengthAlgebra.RootTowerLength.Completion

/-! # 単元の巡回perfectoid商の長さ

単元のperfectoidイデアルは全体なので、商は零である。
冪級数表示・次元・perfectoid化への全射性は、この場合に必要ない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open IsLocalRing Section2 RootTowerLength

/-- 単元gの巡回商は、基底極大イデアルの任意の冪に対して長さ零。 -/
theorem completedLength_cyclic_unit_eq_zero
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ i, t i ∈ maximalIdeal A)
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p)
    (g : A) (hg : IsUnit g) (n : ℕ) :
    (completedNormalizedLength A t p ht).len
      (CompletedTower A t p ⧸ ((completedTowerMaxIdeal A t p) ^ n ⊔
        perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g))) =
      0 := by
  have hI := perfectoidIdeal_eq_top_of_isUnit (CompletedTower A t p) p hperf
    (algebraMap A (CompletedTower A t p) g) (hg.map (algebraMap A (CompletedTower A t p)))
  have htop : (completedTowerMaxIdeal A t p) ^ n ⊔
      perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g) =
      ⊤ := by rw [hI, sup_top_eq]
  let : Subsingleton (CompletedTower A t p ⧸ ((completedTowerMaxIdeal A t p) ^ n ⊔
      perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g))) :=
    Ideal.Quotient.subsingleton_iff.mpr htop
  exact (completedNormalizedLength A t p ht).len_eq_zero_of_subsingleton _

end SerrePositivity.CLMST
