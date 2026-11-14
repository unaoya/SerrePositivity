module

public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawCoefficients
public import SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDSmallRawEnvelope
public import SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittPDBase
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRelativeFree
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Comparison.PDRawCoefficients
import all SerrePositivity.BhattScholze.Prismatic.Crystalline.Envelopes.PDSmallRawEnvelope
import all SerrePositivity.BhattScholze.Prismatic.HodgeTate.Comparison.Witt.WittPDBase

/-!
# 小さい分冪模型の係数変更と分冪構造

## 概要
分冪基底を保つ係数変更は、未完備の小さい多項式模型の分冪を保つ。

## 方針
イデアルの二種類の生成元を照合する。標的を p で局所化して階乗表示で分冪を比較する。

## 規約
基底は p 正則で p 完備とする。係数変更の分冪との両立を仮定に明記する。

## 使われ方
BS 著者版 Theorem 6.4 の小さい分冪模型の係数変換。
-/

public noncomputable section

open scoped TensorProduct

universe u

namespace SerrePositivity.BhattScholze.Prismatic

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem map_dpow_of_map_le {p : ℕ} [Fact p.Prime]
    {R S : Type u} [CommRing R] [CommRing S] {I : Ideal R} {J : Ideal S}
    (γ : DividedPowers I) (δ : DividedPowers J) (f : R →+* S) (hI : I.map f ≤ J)
    (hreg : Function.Injective (fun x : S => (p : S) * x))
    (hlocal : ∀ m : ℕ, ¬p ∣ m → IsUnit (m : S)) (m : ℕ) (x : R) (hx : x ∈ I) :
    δ.dpow m (f x) = f (γ.dpow m x) := by
  let L := Localization.Away (p : S)
  let a := algebraMap S L
  let : Algebra ℚ L := DeltaStructure.primeDividedPowersAwayRatAlgebra hlocal
  apply away_injective_of_prime p hreg
  apply (IsUnit.natCast_factorial_of_algebra ℚ m (A := L)).mul_left_cancel
  have h₁ := congrArg (a.comp f) (γ.factorial_mul_dpow_eq_pow (n := m) hx)
  have h₂ := congrArg a (δ.factorial_mul_dpow_eq_pow (n := m) (hI (Ideal.mem_map_of_mem f hx)))
  simp only [RingHom.comp_apply, map_mul, map_natCast, map_pow] at h₁ h₂
  exact h₂.trans h₁.symm

variable (p : ℕ) [Fact p.Prime] {k l : Type u} [CommRing k] [CommRing l] [Algebra k l]
variable (r n : ℕ) {J : Ideal k} {I : Ideal l}
variable (γ : DividedPowers J) (ε : DividedPowers I)
variable (hk : IsAdicComplete (Ideal.span {(p : k)}) k)
variable (hl : IsAdicComplete (Ideal.span {(p : l)}) l)
variable (hkreg : Function.Injective (fun x : k => (p : k) * x))
variable (hlreg : Function.Injective (fun x : l => (p : l) * x))
variable (hγ : γ.IsDPMorphism ε (algebraMap k l))

omit [Fact p.Prime] in
include hγ in
private theorem pdRawCoefficients_map_ideal :
    (PDSmallRawEnvelope.ideal (k := k) (J := J) r n).map (pdRawCoefficients k l r n).toRingHom ≤
      PDSmallRawEnvelope.ideal (k := l) (J := I) r n := by
  rw [Ideal.map_le_iff_le_comap, Ideal.span_le, PDRelativeFree.generators]
  rintro x (⟨a, ha, rfl⟩ | ⟨⟨j, z⟩, rfl⟩)
  · change pdRawCoefficients k l r n (algebraMap k (pdRaw k r n) a) ∈
      PDSmallRawEnvelope.ideal (k := l) (J := I) r n
    rw [AlgHom.commutes, IsScalarTower.algebraMap_apply k l (pdRaw l r n)]
    exact PDRelativeFree.coefficient_mem _ _ (hγ.ideal_comp (Ideal.mem_map_of_mem _ ha))
  · change pdRawCoefficients k l r n ((1 : MvPolynomial (Fin r) k) ⊗ₜ[k]
      DividedPowerAlgebra.dp k (j + 1) z) ∈ PDSmallRawEnvelope.ideal (J := I) r n
    rw [pdRawCoefficients_tmul, map_one, DividedPowerAlgebra.map_apply_dp]
    exact PDRelativeFree.dp_mem _ _ (j + 1) (Nat.succ_ne_zero j) _

include hγ in
/-- 未完備の分冪模型の係数変更は分冪射。 -/
theorem pdRawCoefficients_isDPMorphism :
    (PDSmallRawEnvelope.dividedPowers p r n γ hk hkreg).IsDPMorphism
      (PDSmallRawEnvelope.dividedPowers p r n ε hl hlreg)
      (pdRawCoefficients k l r n).toRingHom := by
  have hI : (PDSmallRawEnvelope.ideal (k := k) (J := J) r n).map
      (pdRawCoefficients k l r n).toRingHom ≤ PDSmallRawEnvelope.ideal (k := l) (J := I) r n :=
    pdRawCoefficients_map_ideal (k := k) (l := l) r n γ ε hγ
  have hregular : Function.Injective (fun x : pdRaw l r n => (p : pdRaw l r n) * x) := by
    intro x y h
    apply PDSmallRawEnvelope.raw_regular p r n hlreg
    exact h
  have hlocal (m : ℕ) (hm : ¬p ∣ m) : IsUnit (m : pdRaw l r n) := by
    simpa only [map_natCast] using
      (PDSmallRawEnvelope.isUnit_natCast_of_not_dvd p hl m hm).map (algebraMap l (pdRaw l r n))
  let D₁ := PDSmallRawEnvelope.dividedPowers p r n γ hk hkreg
  let D₂ := PDSmallRawEnvelope.dividedPowers p r n ε hl hlreg
  let f := (pdRawCoefficients k l r n).toRingHom
  change D₁.IsDPMorphism D₂ f
  refine ⟨hI, fun {m} x hx => ?_⟩
  have h := @map_dpow_of_map_le p inferInstance (pdRaw k r n) (pdRaw l r n)
    inferInstance inferInstance _ _ D₁ D₂ f hI hregular hlocal m x hx
  exact h

end SerrePositivity.BhattScholze.Prismatic
