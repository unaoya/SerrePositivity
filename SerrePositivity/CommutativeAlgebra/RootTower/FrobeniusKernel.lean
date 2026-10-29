module

public import SerrePositivity.CommutativeAlgebra.RegularPowerDivisibility
public import SerrePositivity.CommutativeAlgebra.RootTower.CompletedRepresentatives
public import SerrePositivity.CommutativeAlgebra.RootTower.CompletedTilt
public import SerrePositivity.CommutativeAlgebra.RootTower.ModPInjectivity
public import SerrePositivity.CommutativeAlgebra.RootTower.CompletedFrobenius
public import SerrePositivity.CommutativeAlgebra.Witt.PowerSeries

/-! # 完備塔の最初のmod p Frobenius核

有限段の根による商の被約性から、p乗のp整除性をpの最初の根の整除性へ移す。
完備塔の代表を十分先の段へ移すことで、完備化上の核も計算する。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.Section2
variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]

/-- 正の有限段で、p乗がpの倍数なら最初のp根の像の倍数になる。 -/
theorem stage_pow_mem_p_implies_root_dvd
    (hp : IsSMulRegular A (p : A)) (i : Fin h) (hti : t i = (p : A)) (n : ℕ)
    [IsReduced (TowerStage A t p (n + 1) ⧸ Ideal.span {stageX A t p (n + 1) i})]
    (x : TowerStage A t p (n + 1))
    (hx : x ^ p ∈ Ideal.span {(p : TowerStage A t p (n + 1))}) :
    stageX A t p (n + 1) i ^ (p ^ n) ∣ x := by
  let := towerStage_free A t p (n + 1)
  have hpstage : IsSMulRegular (TowerStage A t p (n + 1))
      (p : TowerStage A t p (n + 1)) := by
    simpa using hp.of_flat (S := TowerStage A t p (n + 1))
  have hpow : stageX A t p (n + 1) i ^ (p ^ (n + 1)) =
      (p : TowerStage A t p (n + 1)) := by
    simpa only [hti, map_natCast] using mk_X_pow A t p (n + 1) i
  have hreg : IsLeftRegular (stageX A t p (n + 1) i) := by
    apply (IsLeftRegular.pow_iff (pow_pos (Fact.out : p.Prime).pos (n + 1))).mp
    change Function.Injective (fun z ↦ stageX A t p (n + 1) i ^ (p ^ (n + 1)) * z)
    change Function.Injective (fun z : TowerStage A t p (n + 1) ↦
      (p : TowerStage A t p (n + 1)) * z) at hpstage
    simpa only [hpow] using hpstage
  apply regular_pow_dvd_of_pow_dvd _ _ hreg p (Fact.out : p.Prime).pos (p ^ n) x
  rw [← pow_succ', hpow]
  exact Ideal.mem_span_singleton.mp hx

/-- 有限段の根による商が被約なら、完備塔の最初のFrobenius核が最初のp根で生成される。 -/
theorem completedTower_modP_frobenius_kernel_of_stageReduced
    (hp : IsSMulRegular A (p : A)) (i : Fin h) (hti : t i = (p : A))
    (hstage : ∀ n, IsReduced
      (TowerStage A t p (n + 1) ⧸ Ideal.span {stageX A t p (n + 1) i}))
    (z : ModP (CompletedTower A t p) p) : z ^ p = 0 ↔ z ∈
      Ideal.span {(Ideal.Quotient.mk (Ideal.span {(p : CompletedTower A t p)})
        (completedTowerRoot A t p 1 i))} := by
  let C := CompletedTower A t p
  let q := Ideal.Quotient.mk (Ideal.span {(p : C)})
  constructor
  · intro hz
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨m, hm, x, hx⟩ := exists_completedTower_stage_representative A t p a 1 1
    rw [pow_one] at hx
    have hrep : q (algebraMap (TowerStage A t p m) C x) = z := by
      rw [← ha]
      exact (Ideal.Quotient.eq).mpr hx
    have hpow : algebraMap (TowerStage A t p m) C (x ^ p) ∈
        Ideal.span {(p : C)} ^ 1 := by
      rw [pow_one]
      apply Ideal.Quotient.eq_zero_iff_mem.mp
      rw [map_pow, map_pow, hrep, hz]
    obtain ⟨s, hms, hs⟩ := exists_towerMap_mem_p_pow_of_completed A t p m 1 (x ^ p) hpow
    cases s with
    | zero => omega
    | succ n =>
      let y := towerMap A t p m (n + 1) hms x
      have hy : y ^ p ∈ Ideal.span {(p : TowerStage A t p (n + 1))} := by
        simpa only [pow_one, map_pow] using hs
      let := hstage n
      obtain ⟨b, hb⟩ := stage_pow_mem_p_implies_root_dvd A t p hp i hti n y hy
      have hroot : algebraMap (TowerStage A t p (n + 1)) C
          (stageX A t p (n + 1) i) ^ (p ^ n) = completedTowerRoot A t p 1 i := by
        change completedTowerRoot A t p (n + 1) i ^ (p ^ n) = _
        simpa only [Nat.add_sub_cancel] using
          completedTowerRoot_pow_of_le A t p 1 (n + 1) (by omega) i
      apply Ideal.mem_span_singleton.mpr
      refine ⟨q (algebraMap (TowerStage A t p (n + 1)) C b), ?_⟩
      calc
        z = q (algebraMap (TowerStage A t p m) C x) := hrep.symm
        _ = q (algebraMap (TowerStage A t p (n + 1)) C y) := by
          dsimp only [y]
          rw [completedTower_algebraMap_towerMap]
        _ = _ := by rw [hb, map_mul, map_pow, hroot, map_mul]
  · intro hz
    obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.mp hz
    rw [hb, mul_pow, ← map_pow]
    have hr : completedTowerRoot A t p 1 i ^ p = (p : C) := by
      simpa only [pow_one, hti, map_natCast] using completedTowerRoot_pow A t p 1 i
    rw [hr]
    have hq : q (p : C) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
    rw [hq, zero_mul]

/-- 最小パラメータ系の場合の、完備塔の最初のmod p Frobenius核の計算。 -/
theorem completedTower_modP_frobenius_kernel_of_parameters
    [IsLocalRing A] [IsNoetherianRing A] {r : ℕ} (t : Fin (r + 1) → A)
    (hp : IsSMulRegular A (p : A))
    (ht : Ideal.span (Set.range t) = IsLocalRing.maximalIdeal A)
    (hti : t 0 = (p : A)) (hdim : ringKrullDim A = r + 1)
    (z : ModP (CompletedTower A t p) p) : z ^ p = 0 ↔ z ∈
      Ideal.span {(Ideal.Quotient.mk (Ideal.span {(p : CompletedTower A t p)})
        (completedTowerRoot A t p 1 0))} := by
  apply completedTower_modP_frobenius_kernel_of_stageReduced A t p hp 0 hti _ z
  intro n
  let := stageRootQuotient_isDomain_of_parameters A p t ht hdim (n + 1)
  infer_instance

/-- 最小パラメータ系の完備塔のperfectoid性。核条件は有限段の被約性から証明する。 -/
theorem completedTower_isIntegralPerfectoid_of_parameters
    [IsLocalRing A] [IsNoetherianRing A] {r : ℕ} (t : Fin (r + 1) → A)
    (hp : IsSMulRegular A (p : A))
    (ht : Ideal.span (Set.range t) = IsLocalRing.maximalIdeal A)
    (hti : t 0 = (p : A)) (hdim : ringKrullDim A = r + 1)
    (hF : Function.Surjective (fun x : ModP (CompletedTower A t p) p ↦ x ^ p)) :
    IsIntegralPerfectoid (CompletedTower A t p) p := by
  by_cases hC : Subsingleton (CompletedTower A t p)
  · exact Or.inl hC
  have hnu : ¬ IsUnit (p : CompletedTower A t p) := by
    intro hu
    have heq : Ideal.span {(p : CompletedTower A t p)} = ⊤ :=
      Ideal.span_singleton_eq_top.mpr hu
    have hc : IsAdicComplete (⊤ : Ideal (CompletedTower A t p)) (CompletedTower A t p) := by
      rw [← heq]
      infer_instance
    exact hC hc.subsingleton
  let : Fact (¬ IsUnit (p : CompletedTower A t p)) := ⟨hnu⟩
  exact completedTower_isIntegralPerfectoid_of_frobenius_kernel A t p hp 0 hti hF
    (completedTower_modP_frobenius_kernel_of_parameters A p t hp ht hti hdim)

/-- Witt係数表示と最小パラメータ系から、完備塔のperfectoid性を証明する。
表示から局所性・次元・パラメータ生成を供給する工程は別に明示する。 -/
theorem completedTower_isIntegralPerfectoid_of_wittPresentation_and_parameters
    [IsLocalRing A] [IsNoetherianRing A] {r : ℕ} (t : Fin (r + 1) → A)
    (k : Type u) [CommRing k] [CharP k p] [PerfectRing k p]
    (hp : IsSMulRegular A (p : A))
    (ht : Ideal.span (Set.range t) = IsLocalRing.maximalIdeal A)
    (hti : t 0 = (p : A)) (hdim : ringKrullDim A = r + 1)
    (e : A ≃+* MvPowerSeries (Fin r) (WittVector p k))
    (he : ∀ i : Fin r, e (t i.succ) = MvPowerSeries.X i) :
    IsIntegralPerfectoid (CompletedTower A t p) p := by
  let eP := wittPresentedModPEquiv A (Fin r) k p e
  let f : k →+* A ⧸ Ideal.span {(p : A)} := eP.symm.toRingHom.comp MvPowerSeries.C
  let : CharP (A ⧸ Ideal.span {(p : A)}) p :=
    charP_of_injective_ringHom (f := f) (eP.symm.injective.comp MvPowerSeries.C_injective) p
  apply completedTower_isIntegralPerfectoid_of_parameters A p t hp ht hti hdim
  exact completedTower_modP_pow_surjective_of_powerSeries A t p eP Fin.succ
    (fun i ↦ wittPresentedModPEquiv_coordinate A (Fin r) k p e (t i.succ) i (he i))

end SerrePositivity.Section2
