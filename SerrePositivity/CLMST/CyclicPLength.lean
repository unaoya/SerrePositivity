module

public import SerrePositivity.CLMST.PerfectoidIdealRoots
public import SerrePositivity.LengthAlgebra.RootTowerLength.CoordinateVanishing

/-! # 命題4.0.10の p の場合の数値接続

完備塔の p の全根が perfectoid ideal に属することを、選んだ商の被約性から確認し、
有限段の単項式の上界から巡回商の長さ零へ接続する。
被約性は未実装の perfectoid 基礎定理に依存する条件として明示し、
この条件付き結果を無条件の命題4.0.10の証明とは扱わない。
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

end SerrePositivity.CLMST
