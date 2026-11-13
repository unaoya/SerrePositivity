module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDSmallRawEnvelope
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDSmallRawEnvelope

/-!
# 多項式座標の一部を消す相対分冪包

## 概要
係数を剰余へ送り、座標を多項式変数と零に分ける評価の分冪包を具体化する。

## 方針
残る座標の多項式代数に、消える座標の自由分冪代数をテンソルする。

## 規約
両方の座標集合は任意。係数の p 正則性と p 完備性を明示する。

## 使われ方
Berthelot I.2.3.1 の相対分冪包と、BS 著者版 Theorem 6.4 の大きい枠の正則性。
-/

public noncomputable section

open DividedPowerAlgebra Algebra.TensorProduct
open scoped TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic.PDPolynomialSplitEnvelope

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {k : Type u} [CommRing k] {J : Ideal k} (α σ : Type u)

local notation "Frame" => MvPolynomial (α ⊕ σ) k
local notation "Coeff" => MvPolynomial α k

/-- 左の変数を保ち、右の変数を消す剰余評価。 -/
def evaluate : Frame →ₐ[k] MvPolynomial α (k ⧸ J) :=
  MvPolynomial.aeval (Sum.elim MvPolynomial.X fun _ => 0)

@[simp] theorem evaluate_X_inl (i : α) :
    evaluate (J := J) α σ (MvPolynomial.X (Sum.inl i)) = MvPolynomial.X i :=
  MvPolynomial.aeval_X _ _

@[simp] theorem evaluate_X_inr (j : σ) :
    evaluate (J := J) α σ (MvPolynomial.X (Sum.inr j)) = 0 :=
  MvPolynomial.aeval_X _ _

local notation "K" => RingHom.ker (evaluate (J := J) α σ)

/-- 左の変数の多項式代数と右の変数の自由分冪代数のテンソル積。 -/
abbrev Raw := Coeff ⊗[k] DividedPowerAlgebra k (σ →₀ k)

local notation "RawRing" => Raw (k := k) α σ

private def base (i : α) : RawRing :=
  (includeLeft : Coeff →ₐ[k] RawRing) (MvPolynomial.X i)

private def diff (j : σ) : RawRing :=
  PDRelativeFree.generator Coeff σ 1 (Finsupp.single j 1)

/-- 左の変数は多項式変数へ、右の変数は自由分冪変数へ送る。 -/
def unit : Frame →ₐ[k] RawRing :=
  MvPolynomial.aeval (Sum.elim (base (k := k) α σ) (diff (k := k) α σ))

private theorem kernel_le {E : Type u} [CommRing E] [Algebra k E] (f : Frame →ₐ[k] E)
    (hbase : ∀ a ∈ J, algebraMap k E a = 0) (hvar : ∀ j, f (MvPolynomial.X (Sum.inr j)) = 0) :
    K ≤ RingHom.ker f := by
  let g : MvPolynomial α (k ⧸ J) →+* E :=
    MvPolynomial.eval₂Hom (Ideal.Quotient.lift J (algebraMap k E) hbase)
      (fun i => f (MvPolynomial.X (Sum.inl i)))
  have hf : f.toRingHom = g.comp (evaluate (J := J) α σ).toRingHom := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change f (MvPolynomial.C a) = g (evaluate (J := J) α σ (MvPolynomial.C a))
      have he : evaluate (J := J) α σ (MvPolynomial.C a) =
          MvPolynomial.C (Ideal.Quotient.mk J a) :=
        (evaluate (J := J) α σ).commutes a
      rw [he, ← MvPolynomial.algebraMap_eq, f.commutes]
      simp [g]
    · intro x
      change f (MvPolynomial.X x) = g (evaluate (J := J) α σ (MvPolynomial.X x))
      rw [evaluate, MvPolynomial.aeval_X]
      cases x with
      | inl i =>
        change f (MvPolynomial.X (Sum.inl i)) = g (MvPolynomial.X i)
        exact (MvPolynomial.eval₂Hom_X' (Ideal.Quotient.lift J (algebraMap k E) hbase)
          (fun i => f (MvPolynomial.X (Sum.inl i))) i).symm
      | inr j => exact (hvar j).trans (map_zero g).symm
  intro x hx
  change f.toRingHom x = 0
  rw [hf, RingHom.comp_apply]
  change g (evaluate (J := J) α σ x) = 0
  rw [RingHom.mem_ker.mp hx, map_zero]

private theorem unit_map_le :
    (K).map (unit (k := k) α σ) ≤ PDRelativeFree.ideal Coeff σ J := by
  let I : Ideal Frame := Ideal.span (MvPolynomial.C '' (J : Set k) ∪
    Set.range (fun j : σ => MvPolynomial.X (Sum.inr j)))
  let f : Frame →ₐ[k] Frame ⧸ I := Ideal.Quotient.mkₐ k I
  have h := kernel_le (J := J) α σ f
    (fun a ha => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Or.inl ⟨a, ha, rfl⟩)))
    (fun j => Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Or.inr ⟨j, rfl⟩)))
  rw [Ideal.map_le_iff_le_comap]
  apply (show K ≤ I from fun _ hx => Ideal.Quotient.eq_zero_iff_mem.mp (h hx)).trans
  apply Ideal.span_le.mpr
  rintro _ (⟨a, ha, rfl⟩ | ⟨j, rfl⟩)
  · change unit (k := k) α σ (MvPolynomial.C a) ∈ PDRelativeFree.ideal Coeff σ J
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes]
    exact PDRelativeFree.coefficient_mem Coeff σ ha
  · change unit (k := k) α σ (MvPolynomial.X (Sum.inr j)) ∈ PDRelativeFree.ideal Coeff σ J
    rw [unit, MvPolynomial.aeval_X]
    exact PDRelativeFree.dp_mem Coeff σ 1 one_ne_zero _

variable (p : ℕ) [Fact p.Prime] (γ : DividedPowers J)

local notation "L" => Localization.Away (p : Coeff)
variable (hk : IsAdicComplete (Ideal.span {(p : k)}) k)
variable (hreg : Function.Injective (fun x : k => (p : k) * x))

omit [Fact p.Prime] in
include hreg in
private theorem coefficient_regular : IsRegular (p : Coeff) := by
  have h : IsSMulRegular Coeff (p : Coeff) := by
    simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
      (show IsSMulRegular k (p : k) from hreg).of_flat (S := Coeff)
  exact ⟨h, fun _ _ hxy => h (by simpa only [smul_eq_mul, mul_comm (p : Coeff)] using hxy)⟩

omit [Fact p.Prime] in
include hreg in
private theorem localization_injective : Function.Injective (algebraMap Coeff L) := by
  apply (IsLocalization.injective_iff_isRegular (Submonoid.powers (p : Coeff)) (S := L)).mpr
  rintro ⟨x, m, rfl⟩
  exact (coefficient_regular α p hreg).pow m

@[instance_reducible] private def rationalAlgebra : Algebra ℚ L :=
  DeltaStructure.primeDividedPowersAwayRatAlgebra fun m hm => by
    simpa only [map_natCast] using
      (PDSmallRawEnvelope.isUnit_natCast_of_not_dvd p hk m hm).map (algebraMap k Coeff)

/-- 左の変数を係数側に置き、右の変数に自由分冪を入れる。 -/
def dividedPowers : DividedPowers (A := RawRing) (PDRelativeFree.ideal Coeff σ J) :=
  let := rationalAlgebra α p hk
  PDRelativeFree.dividedPowers Coeff σ L (localization_injective α p hreg) γ

variable {E : Type u} [CommRing E] [Algebra k E] {I' : Ideal E}
variable (ε : DividedPowers I') (f : MvPolynomial (α ⊕ σ) k →ₐ[k] E)
variable (hf : (RingHom.ker (evaluate (k := k) (J := J) α σ).toRingHom).map f ≤ I')

private def targetDiff : (σ →₀ k) →ₗ[k] E :=
  Finsupp.linearCombination k fun j => f (MvPolynomial.X (Sum.inr j))

include hf in
private theorem targetDiff_mem (x : σ →₀ k) : targetDiff α σ f x ∈ I' := by
  classical
  rw [targetDiff, Finsupp.linearCombination_apply]
  apply I'.sum_mem
  intro j hj
  dsimp only
  rw [Algebra.smul_def]
  apply I'.mul_mem_left
  apply hf
  apply Ideal.mem_map_of_mem
  change evaluate (J := J) α σ (MvPolynomial.X (Sum.inr j)) = 0
  exact MvPolynomial.aeval_X _ _

include hk hreg in
private theorem hom_ext {g₁ g₂ : RawRing →ₐ[k] E}
    (h₁ : (dividedPowers α σ p γ hk hreg).IsDPMorphism ε g₁.toRingHom)
    (h₂ : (dividedPowers α σ p γ hk hreg).IsDPMorphism ε g₂.toRingHom)
    (he : g₁.comp (unit α σ) = g₂.comp (unit α σ)) : g₁ = g₂ := by
  let := rationalAlgebra α p hk
  have hb i : g₁ (base α σ i) = g₂ (base α σ i) := by
    have h := DFunLike.congr_fun he (MvPolynomial.X (Sum.inl i))
    simpa only [AlgHom.comp_apply, unit, MvPolynomial.aeval_X, Sum.elim_inl] using h
  have hd j : g₁ (diff α σ j) = g₂ (diff α σ j) := by
    have h := DFunLike.congr_fun he (MvPolynomial.X (Sum.inr j))
    simpa only [AlgHom.comp_apply, unit, MvPolynomial.aeval_X, Sum.elim_inr] using h
  apply Algebra.TensorProduct.ext
  · exact MvPolynomial.algHom_ext hb
  · apply DividedPowerAlgebra.algHom_ext
    intro m x
    let d : (σ →₀ k) →ₗ[k] RawRing :=
      (includeRight : DividedPowerAlgebra k (σ →₀ k) →ₐ[k] RawRing).toLinearMap.comp
        (DividedPowerAlgebra.embed k (σ →₀ k))
    have hlin : g₁.toLinearMap.comp d = g₂.toLinearMap.comp d :=
      (Finsupp.basisSingleOne (R := k)).ext hd
    have hdp := PDRelativeFree.dividedPowers_dp_one Coeff σ L
      (localization_injective α p hreg) γ m x
    have hm := PDRelativeFree.dp_mem Coeff σ (J := J) 1 one_ne_zero x
    change g₁.toRingHom (PDRelativeFree.generator Coeff σ m x) =
      g₂.toRingHom (PDRelativeFree.generator Coeff σ m x)
    rw [← hdp]
    change g₁.toRingHom ((dividedPowers α σ p γ hk hreg).dpow m _) =
      g₂.toRingHom ((dividedPowers α σ p γ hk hreg).dpow m _)
    rw [h₁.map_dpow hm, h₂.map_dpow hm]
    exact congrArg (ε.dpow m) (DFunLike.congr_fun hlin x)

/-- 分かれた座標の剰余評価に対する、未完備の相対分冪包の普遍性。 -/
theorem isRelativePDEnvelope :
    IsRelativePDEnvelope γ K (D := RawRing) (dividedPowers α σ p γ hk hreg)
      (unit (k := k) α σ) where
  map_le := unit_map_le α σ
  base_dp := by
    let := rationalAlgebra α p hk
    exact PDRelativeFree.base_isDPMorphism Coeff σ L (localization_injective α p hreg) γ
  lift ε f hf he := by
    let := rationalAlgebra α p hk
    let fB : Coeff →ₐ[k] _ := MvPolynomial.aeval (fun i => f (MvPolynomial.X (Sum.inl i)))
    let G := PDRelativeFree.lift Coeff σ ε fB (targetDiff α σ f) (targetDiff_mem α σ f hf)
    have hG := PDRelativeFree.lift_isDPMorphism Coeff σ L (localization_injective α p hreg)
      γ ε fB (targetDiff α σ f) (targetDiff_mem α σ f hf) he
    have hGc : G.comp (unit α σ) = f := by
      apply MvPolynomial.algHom_ext
      intro x
      change G (unit α σ (MvPolynomial.X x)) = f (MvPolynomial.X x)
      rw [unit, MvPolynomial.aeval_X]
      cases x with
      | inl i =>
        change G ((includeLeft : Coeff →ₐ[k] RawRing) (MvPolynomial.X i)) = _
        exact (PDRelativeFree.lift_includeLeft ..).trans (MvPolynomial.aeval_X _ _)
      | inr j =>
        change G (PDRelativeFree.generator Coeff σ 1 (Finsupp.single j 1)) = _
        rw [show G (PDRelativeFree.generator Coeff σ 1 (Finsupp.single j 1)) =
          ε.dpow 1 (targetDiff α σ f (Finsupp.single j 1)) from
            PDRelativeFree.lift_generator_apply .., ε.dpow_one (targetDiff_mem α σ f hf _)]
        simp [targetDiff, Finsupp.linearCombination_single]
    exact ⟨G, ⟨hG, hGc⟩,
      fun g hg => hom_ext α σ p γ hk hreg ε hg.1 hG (hg.2.trans hGc.symm)⟩

omit [Fact p.Prime] in
include hreg in
/-- 自由分冪模型の p 乗法は係数環の p 乗法が単射なら単射。 -/
theorem raw_regular : IsSMulRegular RawRing (p : RawRing) := by
  let e := freeDPBaseChangeEquiv σ k Coeff
  intro x y h
  apply e.injective
  apply freeDP_isSMulRegular σ (p : Coeff) (coefficient_regular α p hreg).1
  change (p : RawRing) * x = (p : RawRing) * y at h
  simpa only [Algebra.smul_def, map_natCast, map_mul] using congrArg e h

end SerrePositivity.BhattScholze.Prismatic.PDPolynomialSplitEnvelope
