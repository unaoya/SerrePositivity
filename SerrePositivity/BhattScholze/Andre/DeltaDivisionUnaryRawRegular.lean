module

public import SerrePositivity.BhattScholze.Andre.DeltaDivisionUnaryFiniteInitialRegular
public import SerrePositivity.BhattScholze.Andre.DeltaDivisionFiniteRegularStep
public import SerrePositivity.BhattScholze.DeltaDivisionUniversal

/-!
# André E1・E2：正則対上の一元 raw δ 除算包の p 正則性

## 概要

係数環の p,d と mod(p,d) の分子が正則で d が distinguished なら、
全有限関係商および一元 raw δ 除算包は p 正則。
BS Rem 7.15（著者版 p.62）の無限根モニック入力の p 正則性への一般計算。

## 方針

初期段と次段の正則対保存を自然数で帰納し、有限関係イデアルの有向上限へ移す。

## 規約

p 完備性は要求しない。完備化後の p 正則性と prismatic 源の比較は別工程。

## 使われ方

完全 prism 上の無限根モニック raw 包へ補助仮定を具体的に供給して適用する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
variable (hpA : IsSMulRegular A (p : A))
variable (hdA : IsSMulRegular (A ⧸ Ideal.span {(p : A)})
  (Ideal.Quotient.mk (Ideal.span {(p : A)}) d))
variable (haA : IsSMulRegular ((A ⧸ Ideal.span {(p : A)}) ⧸
    Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : A)}) d})
  (Ideal.Quotient.mk (Ideal.span {Ideal.Quotient.mk (Ideal.span {(p : A)}) d})
    (Ideal.Quotient.mk (Ideal.span {(p : A)}) (a default))))
variable (hgL : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (v : Aˣ) (hv : (v : A) = D.delta d)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "I" => deltaDivisionFiniteRelationIdeal D d a
local notation "J" => DeltaStructure.deltaClosure (relativeFreeDeltaStructure σ D)
  (deltaDivisionRelationIdeal d a)
local notation "Raw" => DeltaAdjoinDivision D d a
include hpA hdA haA hgL hv

/-- 概要：全有限 δ 関係商で p と mod p の d は正則。
方針：初期線形関係商から、Witt 正則性による次段保存を帰納する。
規約：分子族は一元添字型上の任意の族。
使われ方：BS Rem 7.15（著者版 p.62）の raw 全体の p 飽和性への入力。 -/
theorem deltaDivisionUnaryFinite_all_regular (N : ℕ) :
    let B := L₀ ⧸ I N
    IsSMulRegular B (p : B) ∧
      IsSMulRegular (B ⧸ Ideal.span {(p : B)})
        (Ideal.Quotient.mk (Ideal.span {(p : B)})
          (Ideal.Quotient.mk (I N) (MvPolynomial.C d))) := by
  induction N with
  | zero =>
    let e : (L₀ ⧸ Ideal.span {deltaDivisionIteratedRelation D d a default 0}) ≃+* L₀ ⧸ I 0 :=
      Ideal.quotEquivOfEq (deltaDivisionUnaryFiniteIdeal_zero D d a).symm
    have h := deltaDivisionUnaryFirst_regular D d a hpA hdA haA
    have ht := ringEquiv_prime_pair_regular e p
      (Ideal.Quotient.mk _ (MvPolynomial.C d)) h.1 h.2
    simpa only [e, Ideal.quotEquivOfEq_mk] using ht
  | succ N ih =>
    exact deltaDivisionUnaryFinite_step_regular D hpA hgL d a v hv N ih.1 ih.2

/-- 概要：実 δ 関係イデアルは p で飽和している。
方針：有限関係イデアルの有向上限から一段へ降り、そこで p を消去する。
規約：全 δ 閉包を有限段で近似する。
使われ方：BS Rem 7.15（著者版 p.62）の一元 raw 包の新しい p ねじれの排除。 -/
theorem deltaDivisionUnaryRaw_relationIdeal_p_saturated (f : L₀) (hf : (p : L₀) * f ∈ J) :
    f ∈ J := by
  rw [deltaDivision_deltaClosure_eq_iSup_finiteRelations] at hf ⊢
  obtain ⟨N, hN⟩ := (Submodule.mem_iSup_of_directed _
    (deltaDivisionFiniteRelationIdeal_mono D d a).directed_le).mp hf
  have hpN := (deltaDivisionUnaryFinite_all_regular D d a hpA hdA haA hgL v hv N).1
  have hz : Ideal.Quotient.mk (I N) f = 0 := by
    apply hpN
    change (p : L₀ ⧸ I N) * Ideal.Quotient.mk (I N) f = (p : L₀ ⧸ I N) * 0
    rw [mul_zero, ← map_natCast (Ideal.Quotient.mk (I N)) p, ← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hN
  exact (le_iSup I N) (Ideal.Quotient.eq_zero_iff_mem.mp hz)

/-- 概要：正則対と正則分子を持つ一元 raw δ 除算包そのものは p 正則。
方針：係数商の p 飽和性を代表元へ適用する。
規約：ねじれを除く新しい商へ取り替えない。
使われ方：BS Rem 7.15（著者版 p.62）の実完備化の前の p 正則性。 -/
theorem deltaDivisionUnaryRaw_p_mul_injective :
    Function.Injective (fun r : Raw => (p : Raw) * r) := by
  let q := Ideal.Quotient.mk J
  intro x z hxz
  change (p : Raw) * x = (p : Raw) * z at hxz
  apply sub_eq_zero.mp
  obtain ⟨f, hf⟩ := Ideal.Quotient.mk_surjective (x - z)
  have hpf : q ((p : L₀) * f) = 0 := by
    rw [map_mul, map_natCast, hf, mul_sub, hxz, sub_self]
  have hm := deltaDivisionUnaryRaw_relationIdeal_p_saturated D d a hpA hdA haA hgL v hv f
    (Ideal.Quotient.eq_zero_iff_mem.mp hpf)
  exact hf.symm.trans (Ideal.Quotient.eq_zero_iff_mem.mpr hm)

end SerrePositivity.BhattScholze.Andre
