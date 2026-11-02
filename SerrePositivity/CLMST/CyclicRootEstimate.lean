module

public import SerrePositivity.CLMST.RootFiltrationBound
public import SerrePositivity.CLMST.PerfectoidFrobeniusComparison

/-! # 巡回perfectoid商の有限段の長さ評価への接続

perfectoid化への全射性を明示的に受け、根の代表元・合同式・有限段の通常長さによる
上界を同時に供給する。一般gでこの上界が零へ収束するという低次元評価はまだ使わない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.CLMST
open Section2 IsLocalRing RootTowerLength
open scoped ENNReal

/-- 原典4.0.10の有限段の根と長さ上界までの接続。
全射性は仮定として残し、低次元の成長評価を結論へ埋め込まない。 -/
theorem exists_cyclic_root_stage_length_estimate
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ j, t j ∈ maximalIdeal A)
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p) (g : A)
    (hsurj :
      letI : Algebra.FinitePresentation (CompletedTower A t p)
          (CompletedTower A t p ⧸ Ideal.span {algebraMap A (CompletedTower A t p) g}) :=
        Algebra.FinitePresentation.quotient
          (Submodule.fg_span_singleton (algebraMap A (CompletedTower A t p) g))
      Function.Surjective (toQuotientPerfectoidization (CompletedTower A t p)
        (Ideal.span {algebraMap A (CompletedTower A t p) g}) p hperf))
    (i : Fin h) (hti : t i = (p : A)) (n m₀ : ℕ) :
    let K := completedTowerMaxIdeal A t p ⊔
      perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g)
    ∃ (m : ℕ) (_ : m₀ ≤ m) (_ : n ≤ m) (z : TowerStage A t p m),
      z ^ (p ^ n) - algebraMap A (TowerStage A t p m) g ∈
        Ideal.span {(p : TowerStage A t p m)} ∧
      (completedNormalizedLength A t p ht).len (CompletedTower A t p ⧸ K) ≤
        (p : ℝ≥0∞) ^ n *
          ((Module.length (TowerStage A t p m)
            (TowerStage A t p m ⧸ stageRootRepresentativeIdeal A t p n m i z) : ℝ≥0∞) /
              (stageRank h p m : ℝ≥0∞)) := by
  let I := perfectoidIdeal (CompletedTower A t p) p hperf
    (algebraMap A (CompletedTower A t p) g)
  let K := completedTowerMaxIdeal A t p ⊔ I
  obtain ⟨m, hm, hnm, z, hz, hmem⟩ :=
    exists_stage_root_mem_sup_perfectoidIdeal_of_surjective A t p hperf g hsurj i hti n m₀
  refine ⟨m, hm, hnm, z, hz,
    completedLength_quotient_le_stage_root_estimate A t p ht K le_sup_left i hti n m hnm z ?_⟩
  have hle : Ideal.span {Section2.completedTowerRoot A t p n i} ⊔ I ≤
      K ⊔ Ideal.span {Section2.completedTowerRoot A t p n i} :=
    sup_le le_sup_right (le_sup_of_le_left le_sup_right)
  exact hle hmem

end SerrePositivity.CLMST
