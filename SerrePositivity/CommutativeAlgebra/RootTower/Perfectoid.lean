module

public import SerrePositivity.CommutativeAlgebra.RootTower.CompletedRoots
public import SerrePositivity.CommutativeAlgebra.RootTower.Completion
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Fontaine
public import Mathlib.RingTheory.AdicCompletion.Completeness
public import SerrePositivity.CommutativeAlgebra.RootTower.ModP
public import SerrePositivity.CommutativeAlgebra.Perfectoid.Torsion
public import SerrePositivity.CommutativeAlgebra.PowerSeries.Basic
public import SerrePositivity.CommutativeAlgebra.Witt.PowerSeries
public import SerrePositivity.CommutativeAlgebra.RegularSequence
public import SerrePositivity.CommutativeAlgebra.PowerSeries.Completeness
public import SerrePositivity.CommutativeAlgebra.PowerSeries.Dimension

/-! # 完備した根の塔の perfectoid 性

## 概要

完備塔の mod p Frobenius が全射であること、最初の mod p Frobenius 核が p の最初の根で生成されることを示し、Witt 係数の標準表示から完備塔が perfectoid であることを結論する。

## 方針

有限段の Frobenius 評価の全射性と有限段の代表を使って完備塔へ移す。核は有限段の根による商の被約性から計算する。表示は p 正則性・局所性・次元・極大イデアルの生成を供給する。

## 規約

perfectoid 性の判定（CompatibleRootsPerfectoid）・Witt の import を持つので `RootTower/CompletedRoots` と分け、CLMST の大部分にこれらを持ち込まない。perfectoid 化の存在引用は仮定しない。名前空間は `SerrePositivity.Section2`。

## 使われ方

Inputs/PerfectoidTower（論文の完備塔が perfectoid であるという入力）。
-/

@[expose] public noncomputable section

universe u

section CompletedTiltPart

namespace SerrePositivity.Section2
variable (A : Type*) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    [Fact (¬ IsUnit (p : CompletedTower A t p))]

omit [Fact (¬ IsUnit (p : CompletedTower A t p))] in
/-- 完備塔は自身のpで生成されるイデアルについて完備。 -/
instance completedTower_isAdicComplete_span_p :
    IsAdicComplete (Ideal.span {(p : CompletedTower A t p)}) (CompletedTower A t p) := by
  simpa only [Ideal.map_span, Set.image_singleton, map_natCast] using
    (IsAdicComplete.map_algebraMap_iff (Ideal.span {(p : Tower A t p)})
      (CompletedTower A t p)).mpr (AdicCompletion.isAdicComplete (Submodule.fg_span_singleton _))

/-- 完備塔のperfectoid性を、最初のmod p Frobenius核の計算へ帰着する。
基底環のp正則性と塔の実際の両立する根を使用し、perfectoid性の引用は使わない。 -/
theorem completedTower_isIntegralPerfectoid_of_frobenius_kernel
    (hp : IsSMulRegular A (p : A)) (i : Fin h) (hti : t i = (p : A))
    (hF : Function.Surjective (frobenius (ModP (CompletedTower A t p) p) p))
    (hker : ∀ z : ModP (CompletedTower A t p) p, z ^ p = 0 ↔ z ∈
      Ideal.span {(Ideal.Quotient.mk (Ideal.span {(p : CompletedTower A t p)})
        (completedTowerRoot A t p 1 i))}) : IsIntegralPerfectoid (CompletedTower A t p) p := by
  apply isIntegralPerfectoid_of_compatible_p_roots (CompletedTower A t p) p
    (isSMulRegular_p_completedTower A t p hp) hF
    (fun n ↦ completedTowerRoot A t p n i) _
    (fun n ↦ completedTowerRoot_succ_pow A t p n i) hker
  simp only [completedTowerRoot_zero, hti, map_natCast]

end SerrePositivity.Section2

end CompletedTiltPart

section CompletedFrobeniusPart

namespace SerrePositivity.Section2
open MvPolynomial
variable (A : Type u) [CommRing A] {h : ℕ} (t : Fin h → A) (p : ℕ) [Fact p.Prime]
    [CharP (A ⧸ Ideal.span {(p : A)}) p]

/-- 有限段のFrobenius評価は、任意のA代数への写像のmod pにおける冪と両立する。 -/
theorem stageModPFrobenius_map_eq_pow
    (S : Type u) [CommRing S] [Algebra A S] (n : ℕ)
    (f : TowerStage A t p n →ₐ[A] S) (z : TowerStage A t p n) :
    modPMap p (algebraMap A S) (stageModPFrobenius A t p n z) =
      (Ideal.Quotient.mk (Ideal.span {(p : S)}) (f z)) ^ (p ^ n) := by
  classical
  by_cases hsub : Subsingleton (ModP S p)
  · exact hsub.elim _ _
  let : Nontrivial (ModP S p) := not_subsingleton_iff_nontrivial.mp hsub
  let : CharP (ModP S p) p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
    rw [← map_natCast (Ideal.Quotient.mk (Ideal.span {(p : S)}))]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)))
  let q := Ideal.Quotient.mk (Ideal.span {(p : S)})
  have heq : (modPMap p (algebraMap A S)).comp (stageModPFrobenius A t p n) =
      (iterateFrobenius (ModP S p) p n).comp (q.comp f.toRingHom) := by
    apply Ideal.Quotient.ringHom_ext
    apply MvPolynomial.ringHom_ext
    · intro a
      change modPMap p (algebraMap A S)
          (stageModPFrobenius A t p n (algebraMap A _ a)) =
        q (f (algebraMap A _ a)) ^ (p ^ n)
      rw [stageModPFrobenius_algebraMap, map_pow, f.commutes]
      rfl
    · intro i
      change modPMap p (algebraMap A S)
          (stageModPFrobenius A t p n (stageX A t p n i)) =
        q (f (stageX A t p n i)) ^ (p ^ n)
      rw [stageModPFrobenius_stageX]
      change q (algebraMap A S (t i)) = q (f (stageX A t p n i)) ^ (p ^ n)
      rw [← map_pow, ← map_pow]
      change q (algebraMap A S (t i)) = q (f
        (Ideal.Quotient.mk (towerRel A t p n) (X i) ^ (p ^ n)))
      rw [mk_X_pow, f.commutes]
  exact DFunLike.congr_fun heq z

/-- 一段のFrobenius評価が全射なら、完備塔のmod pの全ての元がp乗になる。 -/
theorem completedTower_modP_pow_surjective_of_stageFrobenius_surjective
    (hstage : Function.Surjective (stageModPFrobenius A t p 1)) :
    Function.Surjective (fun x : ModP (CompletedTower A t p) p ↦ x ^ p) := by
  classical
  let C := CompletedTower A t p
  let Q := ModP C p
  let q : C →+* Q := Ideal.Quotient.mk (Ideal.span {(p : C)})
  by_cases hsub : Subsingleton Q
  · let := hsub
    exact fun x ↦ ⟨0, Subsingleton.elim _ _⟩
  let : Nontrivial Q := not_subsingleton_iff_nontrivial.mp hsub
  let : CharP Q p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).mpr (by
    rw [← map_natCast q]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)))
  let F := frobenius Q p
  have hcoeff (a : A) : q (algebraMap A C a) ∈ F.range := by
    obtain ⟨z, hz⟩ := hstage (Ideal.Quotient.mk (Ideal.span {(p : A)}) a)
    refine ⟨q (algebraMap (TowerStage A t p 1) C z), ?_⟩
    have hh := stageModPFrobenius_map_eq_pow A t p C 1
      (IsScalarTower.toAlgHom A (TowerStage A t p 1) C) z
    rw [hz] at hh
    simpa only [pow_one, IsScalarTower.toAlgHom_apply, modPMap,
      Ideal.quotientMap_mk, F, q, frobenius_def] using hh.symm
  have hroot (n : ℕ) (i : Fin h) : q (completedTowerRoot A t p n i) ∈ F.range := by
    refine ⟨q (completedTowerRoot A t p (n + 1) i), ?_⟩
    change q (completedTowerRoot A t p (n + 1) i) ^ p = _
    rw [← map_pow, completedTowerRoot_succ_pow]
  have hfinite (n : ℕ) (z : TowerStage A t p n) :
      q (algebraMap (TowerStage A t p n) C z) ∈ F.range := by
    obtain ⟨φ, rfl⟩ := Ideal.Quotient.mk_surjective z
    induction φ using MvPolynomial.induction_on with
    | C a =>
      change q (algebraMap (TowerStage A t p n) C (algebraMap A _ a)) ∈ F.range
      rw [← IsScalarTower.algebraMap_apply A (TowerStage A t p n) C]
      exact hcoeff a
    | add φ ψ hφ hψ =>
      simp only [map_add]
      exact F.range.add_mem hφ hψ
    | mul_X φ i hφ =>
      simp only [map_mul]
      exact F.range.mul_mem hφ (hroot n i)
  intro x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨n, _, z, hz⟩ := exists_completedTower_stage_representative A t p a 1 0
  have heq : q (algebraMap (TowerStage A t p n) C z) = q a := by
    apply Ideal.Quotient.eq.mpr
    simpa only [pow_one] using hz
  obtain ⟨y, hy⟩ := hfinite n z
  exact ⟨y, hy.trans heq⟩

/-- mod pの標準冪級数表示から、完備塔のmod p Frobeniusの全射性を得る。 -/
theorem completedTower_modP_pow_surjective_of_powerSeries
    {k σ : Type*} [CommRing k] [Finite σ] [CharP k p] [PerfectRing k p]
    (e : A ⧸ Ideal.span {(p : A)} ≃+* MvPowerSeries σ k)
    (ι : σ → Fin h)
    (he : ∀ i, e (Ideal.Quotient.mk (Ideal.span {(p : A)}) (t (ι i))) = MvPowerSeries.X i) :
    Function.Surjective (fun x : ModP (CompletedTower A t p) p ↦ x ^ p) :=
  completedTower_modP_pow_surjective_of_stageFrobenius_surjective A t p
    (stageModPFrobenius_surjective_of_powerSeries t p e ι he 1)

end SerrePositivity.Section2

end CompletedFrobeniusPart

section FrobeniusKernelPart

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

end FrobeniusKernelPart

section WittPresentationPart

namespace SerrePositivity.Section2
open IsLocalRing
variable (A k : Type u) [CommRing A] [Field k] (p : ℕ)
    [Fact p.Prime] [CharP k p] [PerfectField k]

/-- 標準Witt係数表示から、追加の局所環・次元の仮定なしにperfectoid性を証明する。 -/
theorem completedTower_isIntegralPerfectoid_of_wittPresentation
    {r : ℕ} (t : Fin (r + 1) → A) (hti : t 0 = (p : A))
    (e : A ≃+* MvPowerSeries (Fin r) (WittVector p k))
    (he : ∀ i : Fin r, e (t i.succ) = MvPowerSeries.X i) :
    IsIntegralPerfectoid (CompletedTower A t p) p := by
  let B := MvPowerSeries (Fin r) (WittVector p k)
  let : IsLocalRing A := e.symm.isLocalRing
  let : IsNoetherianRing A := isNoetherianRing_of_ringEquiv B e.symm
  let : IsDomain A := e.toMulEquiv.isDomain B
  have hp0 : (p : A) ≠ 0 := by
    intro hp
    have hh := congrArg (fun a : A ↦ MvPowerSeries.constantCoeff (e a)) hp
    simp only [map_natCast, map_zero] at hh
    exact WittVector.p_nonzero p k hh
  have hp : IsSMulRegular A (p : A) := (IsRegular.of_ne_zero hp0).left.isSMulRegular
  have hdim : ringKrullDim A = r + 1 := by
    rw [RingEquiv.ringKrullDim e]
    simpa only [Fintype.card_fin, add_comm] using ringKrullDim_wittPowerSeries (Fin r) k p
  have ht : Ideal.span (Set.range t) = maximalIdeal A := by
    apply (Ideal.comap_injective_of_surjective e.symm.toRingHom e.symm.surjective)
    change (Ideal.span (Set.range t)).comap e.symm = (maximalIdeal A).comap e.symm
    simp only [Ideal.comap_symm]
    rw [Ideal.map_span, map_ringEquiv_maximalIdeal, wittPowerSeries_maximalIdeal_eq]
    have hset : e '' Set.range t = {(p : B)} ∪ Set.range (MvPowerSeries.X (σ := Fin r)
        (R := WittVector p k)) := by
      ext x
      constructor
      · rintro ⟨a, ⟨i, rfl⟩, rfl⟩
        refine Fin.cases ?_ (fun j ↦ ?_) i
        · left; simp [hti]
        · right; exact ⟨j, (he j).symm⟩
      · rintro (hx | ⟨i, rfl⟩)
        · refine ⟨t 0, Set.mem_range_self _, ?_⟩
          have hx' : x = (p : B) := hx
          simpa only [hti, map_natCast] using hx'.symm
        · exact ⟨t i.succ, Set.mem_range_self _, he i⟩
    rw [hset, Ideal.span_union]
  exact completedTower_isIntegralPerfectoid_of_wittPresentation_and_parameters A p t k
    hp ht hti hdim e he

/-- 零番以外の座標の添字を、順序を保ったFin rへ移す。 -/
def nonzeroCoordinateEquiv (r : ℕ) : {i : Fin (r + 1) // (i : ℕ) ≠ 0} ≃ Fin r where
  toFun i := ⟨(i.val : ℕ) - 1, by have := i.val.isLt; have := i.property; omega⟩
  invFun i := ⟨i.succ, by simp⟩
  left_inv i := by
    apply Subtype.ext
    apply Fin.ext
    have := i.property
    simp only [Fin.val_succ]
    omega
  right_inv i := by apply Fin.ext; simp

/-- 原典の添字と同じ標準Witt係数表示から、完備塔のperfectoid性を証明する。 -/
theorem completedTower_isIntegralPerfectoid_of_standard_wittPresentation
    {h : ℕ} (t : Fin h → A) (hpos : 0 < h) (hti : t ⟨0, hpos⟩ = (p : A))
    (e : A ≃+* MvPowerSeries {i : Fin h // (i : ℕ) ≠ 0} (WittVector p k))
    (he : ∀ i hi, e (t i) = MvPowerSeries.X ⟨i, hi⟩) :
    IsIntegralPerfectoid (CompletedTower A t p) p := by
  cases h with
  | zero => omega
  | succ r =>
    let e' := e.trans (MvPowerSeries.renameEquiv (WittVector p k)
      (nonzeroCoordinateEquiv r)).toRingEquiv
    apply completedTower_isIntegralPerfectoid_of_wittPresentation A k p t hti e'
    intro i
    change MvPowerSeries.rename (nonzeroCoordinateEquiv r) (e (t i.succ)) = _
    rw [he i.succ (by simp), MvPowerSeries.rename_X]
    congr 1

end SerrePositivity.Section2

end WittPresentationPart
