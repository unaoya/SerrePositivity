module

public import SerrePositivity.CLMST.StageModPLengthBound
public import SerrePositivity.CLMST.CyclicRootEstimate
public import SerrePositivity.LengthAlgebra.RootTowerLength.StageDecay
public import SerrePositivity.LengthAlgebra.QuotientBounds
public import SerrePositivity.LengthAlgebra.Almost

/-! # 巡回perfectoid商の一様な正規化上界

具体的な有限段のFrobenius比較と二つの段の差の倍率を正規化に接続する。
perfectoid化への全射性を明示的に受けた場合、pがgを割らない非単元について
c/p^nの上界、長さ零、そして基底極大イデアルの全ての冪による評価を得る。
perfectoid化の全射性そのものはここで証明したとは扱わない。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.CLMST
open IsLocalRing Section2 RootTowerLength
open scoped ENNReal

/-- 有限段の根の代表元による長さ評価を正規化すると、根の指数だけで減少する。 -/
theorem exists_stage_root_normalized_bound
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (t : Fin (r + 2) → A) (p : ℕ) [Fact p.Prime]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A))
    (hdim : ringKrullDim A = r + 2)
    {k σ : Type*} [CommRing k] [Finite σ] [CharP k p] [PerfectRing k p]
    (e : A ⧸ Ideal.span {(p : A)} ≃+* MvPowerSeries σ k) (ι : σ → Fin (r + 2))
    (he : ∀ i, e (Ideal.Quotient.mk (Ideal.span {(p : A)}) (t (ι i))) = MvPowerSeries.X i)
    (g : A) (hgm : g ∈ maximalIdeal A) (hpg : ¬ (p : A) ∣ g) :
    ∃ c : ℕ, ∀ (n m : ℕ) (_ : n ≤ m) (z : TowerStage A t p m),
      z ^ (p ^ n) - algebraMap A (TowerStage A t p m) g ∈
        Ideal.span {(p : TowerStage A t p m)} →
      (p : ℝ≥0∞) ^ n *
        ((Module.length (TowerStage A t p m)
          (TowerStage A t p m ⧸ stageRootRepresentativeIdeal A t p n m 0 z) : ℝ≥0∞) /
            (stageRank (r + 2) p m : ℝ≥0∞)) ≤ (c : ℝ≥0∞) / (p : ℝ≥0∞) ^ n := by
  obtain ⟨c, hc⟩ := exists_stage_root_quotient_length_bound A t p ht htp hdim e ι he g hgm hpg
  refine ⟨c, fun n m hnm z hz ↦ ?_⟩
  have hmm : stageRootRepresentativeIdeal A t p m m 0 z =
      (maximalIdeal A).map (algebraMap A (TowerStage A t p m)) ⊔
        Ideal.span {stageX A t p m 0} ⊔ Ideal.span {z} := by
    simp only [stageRootRepresentativeIdeal, Nat.sub_self, pow_zero, pow_one]
  have hroot : Module.length (TowerStage A t p m)
      (TowerStage A t p m ⧸ stageRootRepresentativeIdeal A t p m m 0 z) ≤
        ((p ^ (m - n) : ℕ) : ℕ∞) * (((p ^ m : ℕ) : ℕ∞) ^ r * (c : ℕ∞)) := by
    rw [(Ideal.quotientEquivAlgOfEq (TowerStage A t p m) hmm).toLinearEquiv.length_eq]
    exact hc n m hnm z hz
  have hlen := (length_stageRootRepresentativeIdeal_le A t p n m 0 z).trans
    (mul_le_mul_right hroot ((p ^ (m - n) : ℕ) : ℕ∞))
  have hlen' : (Module.length (TowerStage A t p m)
      (TowerStage A t p m ⧸ stageRootRepresentativeIdeal A t p n m 0 z) : ℝ≥0∞) ≤
        (p : ℝ≥0∞) ^ (m - n) *
          ((p : ℝ≥0∞) ^ (m - n) * (((p : ℝ≥0∞) ^ m) ^ r * (c : ℝ≥0∞))) := by
    exact_mod_cast hlen
  exact (mul_le_mul_right (ENNReal.div_le_div_right hlen' _) _).trans_eq
    (root_stage_normalization p (Fact.out : p.Prime).ne_zero r n m hnm c)

section Perfectoid
variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A]
    {r : ℕ} (t : Fin (r + 2) → A) (p : ℕ) [Fact p.Prime]
    (htmem : ∀ i, t i ∈ maximalIdeal A)
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A))
    (hdim : ringKrullDim A = r + 2)
    {k σ : Type*} [CommRing k] [Finite σ] [CharP k p] [PerfectRing k p]
    (e : A ⧸ Ideal.span {(p : A)} ≃+* MvPowerSeries σ k) (ι : σ → Fin (r + 2))
    (he : ∀ i, e (Ideal.Quotient.mk (Ideal.span {(p : A)}) (t (ι i))) = MvPowerSeries.X i)
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p) (g : A)
    (hgm : g ∈ maximalIdeal A) (hpg : ¬ (p : A) ∣ g)
    (hsurj :
      letI : Algebra.FinitePresentation (CompletedTower A t p)
          (CompletedTower A t p ⧸ Ideal.span {algebraMap A (CompletedTower A t p) g}) :=
        Algebra.FinitePresentation.quotient
          (Submodule.fg_span_singleton (algebraMap A (CompletedTower A t p) g))
      Function.Surjective (toQuotientPerfectoidization (CompletedTower A t p)
        (Ideal.span {algebraMap A (CompletedTower A t p) g}) p hperf))

include ht htp hdim e ι he hgm hpg hsurj

/-- 根を取る段の選択に依存しない、完備巡回商のc/p^n上界。
perfectoid化への全射性は明示的な適用条件として残る。 -/
theorem exists_completed_cyclic_div_pow_bound_of_surjective :
    let K := completedTowerMaxIdeal A t p ⊔
      perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g)
    ∃ c : ℕ, ∀ n : ℕ,
      (completedNormalizedLength A t p htmem).len (CompletedTower A t p ⧸ K) ≤
        (c : ℝ≥0∞) / (p : ℝ≥0∞) ^ n := by
  obtain ⟨c, hc⟩ := exists_stage_root_normalized_bound A t p ht htp hdim e ι he g hgm hpg
  refine ⟨c, fun n ↦ ?_⟩
  obtain ⟨m, _, hnm, z, hz, hlen⟩ :=
    exists_cyclic_root_stage_length_estimate A t p htmem hperf g hsurj 0 htp n 0
  exact hlen.trans (hc n m hnm z hz)

/-- pがgを割らない非単元の場合、全射性から一次の巡回商の長さ零を導く。 -/
theorem completedLength_cyclic_first_eq_zero_of_surjective :
    (completedNormalizedLength A t p htmem).len
      (CompletedTower A t p ⧸ (completedTowerMaxIdeal A t p ⊔
        perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g))) =
      0 := by
  obtain ⟨c, hc⟩ := exists_completed_cyclic_div_pow_bound_of_surjective
    A t p htmem ht htp hdim e ι he hperf g hgm hpg hsurj
  exact ennreal_eq_zero_of_div_pow_bound _ c p (by simp)
    (by exact_mod_cast (Fact.out : p.Prime).one_lt) hc

/-- 同じ条件で、基底極大イデアルの全ての冪に対する巡回商の長さが零。 -/
theorem completedLength_cyclic_pow_eq_zero_of_surjective (a : ℕ) :
    (completedNormalizedLength A t p htmem).len
      (CompletedTower A t p ⧸ ((completedTowerMaxIdeal A t p) ^ a ⊔
        perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g))) =
      0 := by
  apply LengthAlgebra.cyclic_quotient_pow_length_eq_zero_of_first
    (completedNormalizedLength A t p htmem)
  · exact (maximalIdeal A).fg_of_isNoetherianRing.map _
  · exact completedLength_cyclic_first_eq_zero_of_surjective
      A t p htmem ht htp hdim e ι he hperf g hgm hpg hsurj

end Perfectoid

/-- 標準Witt冪級数表示から、pを因子に持たない非単元の巡回評価へ直接接続する。
全射性の確認とdim(A)≤1の場合、およびp因子の処理はこの主張に含めない。 -/
theorem completedLength_cyclic_pow_eq_zero_of_witt_of_surjective
    (A k : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing k]
    {r : ℕ} (t : Fin (r + 2) → A) (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]
    (ht : Ideal.span (Set.range t) = maximalIdeal A) (htp : t 0 = (p : A))
    (hdim : ringKrullDim A = r + 2)
    (e : A ≃+* MvPowerSeries {i : Fin (r + 2) // (i : ℕ) ≠ 0} (WittVector p k))
    (he : ∀ i hi, e (t i) = MvPowerSeries.X ⟨i, hi⟩)
    (hperf : IsIntegralPerfectoid (CompletedTower A t p) p) (g : A)
    (hgm : g ∈ maximalIdeal A) (hpg : ¬ (p : A) ∣ g)
    (hsurj :
      letI : Algebra.FinitePresentation (CompletedTower A t p)
          (CompletedTower A t p ⧸ Ideal.span {algebraMap A (CompletedTower A t p) g}) :=
        Algebra.FinitePresentation.quotient
          (Submodule.fg_span_singleton (algebraMap A (CompletedTower A t p) g))
      Function.Surjective (toQuotientPerfectoidization (CompletedTower A t p)
        (Ideal.span {algebraMap A (CompletedTower A t p) g}) p hperf))
    (a : ℕ) :
    (completedNormalizedLength A t p
      (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i))).len
      (CompletedTower A t p ⧸ ((completedTowerMaxIdeal A t p) ^ a ⊔
        perfectoidIdeal (CompletedTower A t p) p hperf (algebraMap A (CompletedTower A t p) g))) =
      0 := by
  let σ := {i : Fin (r + 2) // (i : ℕ) ≠ 0}
  let eQ := wittPresentedModPEquiv A σ k p e
  have heQ : ∀ i : σ,
      eQ (Ideal.Quotient.mk (Ideal.span {(p : A)}) (t i.val)) = MvPowerSeries.X i :=
    fun i ↦ wittPresentedModPEquiv_coordinate A σ k p e (t i.val) i (he i.val i.property)
  exact completedLength_cyclic_pow_eq_zero_of_surjective A t p
    (fun i ↦ ht ▸ Ideal.subset_span (Set.mem_range_self i)) ht htp hdim
    eQ Subtype.val heQ hperf g hgm hpg hsurj a

end SerrePositivity.CLMST
