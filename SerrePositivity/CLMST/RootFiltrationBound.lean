module

public import SerrePositivity.CLMST.PerfectoidIdealRoots
public import SerrePositivity.LengthAlgebra.QuotientPowerBound
public import SerrePositivity.LengthAlgebra.RootTowerLength.CompletedQuotientEvaluation

/-! # p冪根を加えた商から元の商へのフィルトレーション評価

CLMST Proposition 4.0.10の第二不等式に対応する倍率p^nを、共通の正規化長さから供給する。
根の指数nと有限段mを分け、通常長さの分母は有限段の階数を保持する。
perfectoid性や一般gの巡回評価の引用は使わない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.CLMST
open Section2 IsLocalRing RootTowerLength
open scoped ENNReal

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    (ht : ∀ j, t j ∈ maximalIdeal A)

/-- pを含む基底極大イデアルの拡大で消える商は、pのp^n乗根を追加した商のp^n倍以下。 -/
theorem completedLength_quotient_le_root_factor
    (K : Ideal (CompletedTower A t p)) (hJK : completedTowerMaxIdeal A t p ≤ K)
    (i : Fin h) (hti : t i = (p : A)) (n : ℕ) :
    (completedNormalizedLength A t p ht).len (CompletedTower A t p ⧸ K) ≤
      (p : ℝ≥0∞) ^ n * (completedNormalizedLength A t p ht).len
        (CompletedTower A t p ⧸ (K ⊔ Ideal.span {completedTowerRoot A t p n i})) := by
  have hpK : (p : CompletedTower A t p) ∈ K := by
    apply hJK
    have hpA : (p : A) ∈ maximalIdeal A := hti ▸ ht i
    simpa only [completedTowerMaxIdeal, map_natCast] using Ideal.mem_map_of_mem
      (algebraMap A (CompletedTower A t p)) hpA
  have hroot : completedTowerRoot A t p n i ^ (p ^ n) ∈ K := by
    simpa only [completedTowerRoot_pow, hti, map_natCast] using hpK
  simpa only [pow_one, Nat.cast_pow] using
    (completedNormalizedLength A t p ht).len_quotient_le_mul_of_pow_mem
      K 1 (by simpa only [pow_one] using hJK) (completedTowerRoot A t p n i) (p ^ n) hroot

/-- 任意の有限段の有限長な商で、根を追加した商を覆えば、元の商の数値上界が得られる。
根の指数nと評価する段mの分母を混同しない。 -/
theorem completedLength_quotient_le_root_factor_stage_length
    (hp : (p : A) ∈ maximalIdeal A) (K : Ideal (CompletedTower A t p))
    (hJK : completedTowerMaxIdeal A t p ≤ K) (i : Fin h) (hti : t i = (p : A))
    (n m : ℕ) (H : Ideal (TowerStage A t p m))
    (hfinite : IsFiniteLength (TowerStage A t p m) (TowerStage A t p m ⧸ H))
    (hJH : completedTowerMaxIdeal A t p ≤
      H.map (algebraMap (TowerStage A t p m) (CompletedTower A t p)))
    (hHK : H.map (algebraMap (TowerStage A t p m) (CompletedTower A t p)) ≤
      K ⊔ Ideal.span {completedTowerRoot A t p n i}) :
    (completedNormalizedLength A t p ht).len (CompletedTower A t p ⧸ K) ≤
      (p : ℝ≥0∞) ^ n *
        ((Module.length (TowerStage A t p m) (TowerStage A t p m ⧸ H) : ℝ≥0∞) /
          (stageRank h p m : ℝ≥0∞)) := by
  refine (completedLength_quotient_le_root_factor A t p ht K hJK i hti n).trans ?_
  have hb := (completedNormalizedLength A t p ht).len_quotient_le_of_pow_le
    1 _ _ (by simpa only [pow_one] using hJH) hHK
  rw [completedNormalizedLength_quotient_eq_length A t p ht hp m H hfinite] at hb
  exact mul_le_mul_right hb _

include ht in
/-- 有限段で基底極大イデアルを含む関係式による商は有限長。
完備塔のイデアルを縮約した商にも使うため、有限長性を仮定として残さない。 -/
theorem isFiniteLength_stage_quotient_of_maximalIdeal_map_le
    (m : ℕ) (H : Ideal (TowerStage A t p m))
    (hH : (maximalIdeal A).map (algebraMap A (TowerStage A t p m)) ≤ H) :
    IsFiniteLength (TowerStage A t p m) (TowerStage A t p m ⧸ H) := by
  let B := TowerStage A t p m
  let Q := B ⧸ H
  let : IsLocalRing B := isLocalRing_towerStage A t p ht m
  let : Module.Finite A B := towerStage_finite A t p m
  let : (maximalIdeal A).IsMaximal := IsLocalRing.maximalIdeal.isMaximal A
  let : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
  have hann : maximalIdeal A ≤ Module.annihilator A Q := by
    intro a ha
    apply Module.mem_annihilator.mpr
    intro q
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective q
    change a • (Ideal.Quotient.mkₐ A H).toLinearMap b = 0
    rw [← (Ideal.Quotient.mkₐ A H).toLinearMap.map_smul]
    rw [Algebra.smul_def]
    change Ideal.Quotient.mk H (algebraMap A B a * b) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr
      (H.mul_mem_right _ (hH (Ideal.mem_map_of_mem _ ha)))
  have hfin : IsFiniteLength A Q := isFiniteLength_of_le_radical_annihilator
    (maximalIdeal A) Q (hann.trans Ideal.le_radical)
  apply Module.length_ne_top_iff.mp
  rw [← length_eq_of_common_residueField (residue_surjective_towerStage A t p ht m)]
  exact Module.length_ne_top_iff.mpr hfin

/-- 根を追加した完備塔のイデアルの縮約で、原典の最初の二つの不等式を評価する。 -/
theorem completedLength_quotient_le_root_contraction_length
    (K : Ideal (CompletedTower A t p)) (hJK : completedTowerMaxIdeal A t p ≤ K)
    (i : Fin h) (hti : t i = (p : A)) (n m : ℕ) :
    let H := (K ⊔ Ideal.span {completedTowerRoot A t p n i}).comap
      (algebraMap (TowerStage A t p m) (CompletedTower A t p))
    (completedNormalizedLength A t p ht).len (CompletedTower A t p ⧸ K) ≤
      (p : ℝ≥0∞) ^ n *
        ((Module.length (TowerStage A t p m) (TowerStage A t p m ⧸ H) : ℝ≥0∞) /
          (stageRank h p m : ℝ≥0∞)) := by
  let H := (K ⊔ Ideal.span {completedTowerRoot A t p n i}).comap
    (algebraMap (TowerStage A t p m) (CompletedTower A t p))
  have hbase : (maximalIdeal A).map (algebraMap A (TowerStage A t p m)) ≤ H := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    change algebraMap (TowerStage A t p m) (CompletedTower A t p)
      (algebraMap A (TowerStage A t p m) a) ∈
        K ⊔ Ideal.span {completedTowerRoot A t p n i}
    rw [← IsScalarTower.algebraMap_apply A (TowerStage A t p m) (CompletedTower A t p)]
    exact (show K ≤ K ⊔ Ideal.span {completedTowerRoot A t p n i} from le_sup_left)
      (hJK (Ideal.mem_map_of_mem _ ha))
  have hJH : completedTowerMaxIdeal A t p ≤
      H.map (algebraMap (TowerStage A t p m) (CompletedTower A t p)) := by
    have hh := Ideal.map_mono (f := algebraMap (TowerStage A t p m) (CompletedTower A t p)) hbase
    simpa only [Ideal.map_map, ← IsScalarTower.algebraMap_eq, completedTowerMaxIdeal] using hh
  exact completedLength_quotient_le_root_factor_stage_length A t p ht (hti ▸ ht i)
    K hJK i hti n m H (isFiniteLength_stage_quotient_of_maximalIdeal_map_le A t p ht m H hbase)
    hJH (Ideal.map_comap_le)

/-- n段のp冪根と根の代表元zをm段の関係式に加えたイデアル。
m≥nではp冪根の代表は座標のp^(m-n)乗である。 -/
def stageRootRepresentativeIdeal (n m : ℕ) (i : Fin h) (z : TowerStage A t p m) :
    Ideal (TowerStage A t p m) :=
  (maximalIdeal A).map (algebraMap A (TowerStage A t p m)) ⊔
    Ideal.span {stageX A t p m i ^ (p ^ (m - n))} ⊔ Ideal.span {z}

/-- 根の代表元の所属から、有限段の明示的な商による長さの上界を得る。
残る低次元評価の対象を、この通常長さそのものとして明示する。 -/
theorem completedLength_quotient_le_stage_root_estimate
    (K : Ideal (CompletedTower A t p)) (hJK : completedTowerMaxIdeal A t p ≤ K)
    (i : Fin h) (hti : t i = (p : A)) (n m : ℕ) (hnm : n ≤ m)
    (z : TowerStage A t p m)
    (hz : algebraMap (TowerStage A t p m) (CompletedTower A t p) z ∈
      K ⊔ Ideal.span {completedTowerRoot A t p n i}) :
    (completedNormalizedLength A t p ht).len (CompletedTower A t p ⧸ K) ≤
      (p : ℝ≥0∞) ^ n *
        ((Module.length (TowerStage A t p m)
          (TowerStage A t p m ⧸ stageRootRepresentativeIdeal A t p n m i z) : ℝ≥0∞) /
          (stageRank h p m : ℝ≥0∞)) := by
  let H := stageRootRepresentativeIdeal A t p n m i z
  have hbase : (maximalIdeal A).map (algebraMap A (TowerStage A t p m)) ≤ H :=
    le_sup_of_le_left le_sup_left
  have hJH : completedTowerMaxIdeal A t p ≤
      H.map (algebraMap (TowerStage A t p m) (CompletedTower A t p)) := by
    have hh := Ideal.map_mono (f := algebraMap (TowerStage A t p m) (CompletedTower A t p)) hbase
    simpa only [Ideal.map_map, ← IsScalarTower.algebraMap_eq, completedTowerMaxIdeal] using hh
  have hHK : H.map (algebraMap (TowerStage A t p m) (CompletedTower A t p)) ≤
      K ⊔ Ideal.span {completedTowerRoot A t p n i} := by
    dsimp only [H, stageRootRepresentativeIdeal]
    rw [Ideal.map_sup, Ideal.map_sup, Ideal.map_map, ← IsScalarTower.algebraMap_eq,
      Ideal.map_span, Ideal.map_span, Set.image_singleton, Set.image_singleton, map_pow]
    change completedTowerMaxIdeal A t p ⊔
      Ideal.span {completedTowerRoot A t p m i ^ (p ^ (m - n))} ⊔
        Ideal.span {algebraMap (TowerStage A t p m) (CompletedTower A t p) z} ≤ _
    rw [completedTowerRoot_pow_of_le A t p n m hnm i]
    exact sup_le (sup_le (hJK.trans le_sup_left) le_sup_right)
      ((Ideal.span_singleton_le_iff_mem _).mpr hz)
  exact completedLength_quotient_le_root_factor_stage_length A t p ht (hti ▸ ht i)
    K hJK i hti n m H (isFiniteLength_stage_quotient_of_maximalIdeal_map_le A t p ht m H hbase)
    hJH hHK

end SerrePositivity.CLMST
