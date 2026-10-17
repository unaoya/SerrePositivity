module

public import SerrePositivity.BhattScholze.Andre.DeltaDivisionUnaryRawRegular

/-!
# André E1・E2：一元 raw δ 包の正則対

## 概要

有限 δ 関係商の mod p の分母正則性を、実 δ 閉包の商へ移す。
BS Rem 7.15（著者版 p.62）の完備化前の正則対を提供する。

## 方針

(p) と有限関係イデアルの和も有向族となる。所属を一有限段へ降ろして分母を消去する。

## 規約

raw 包は元の δ 閉包商のままであり、完備化の正則性は別工程。

## 使われ方

実 (p,d) 完備化への正則対保存の入力。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "I" => deltaDivisionFiniteRelationIdeal D d a
local notation "J" => DeltaStructure.deltaClosure (relativeFreeDeltaStructure σ D)
  (deltaDivisionRelationIdeal d a)
local notation "Raw" => DeltaAdjoinDivision D d a
local notation "K" => Ideal.span {(p : L₀)} ⊔ J

/-- 概要：raw δ 包の通常 mod p は元の自由環の (p)+δ 閉包商と同型。
方針：主関係追加の第三同型定理を使う。
規約：正則性を仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の有限段から raw 包への比較。 -/
def deltaDivisionRawPrimeQuotientEquiv : (Raw ⧸ Ideal.span {(p : Raw)}) ≃+* L₀ ⧸ K :=
  (Ideal.quotEquivOfEq (show Ideal.span {(p : Raw)} =
    Ideal.span {Ideal.Quotient.mk J (p : L₀)} by rw [map_natCast])).trans
    ((idealThenPrincipalQuotEquiv J (p : L₀)).trans (Ideal.quotEquivOfEq (sup_comm _ _)))

/-- 概要：raw 包の mod p 比較は自由環の代表元を保つ。
方針：主関係追加の代表元公式を使う。
規約：全ての自由環元を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の分母正則性の移送。 -/
theorem deltaDivisionRawPrimeQuotientEquiv_mk (t : L₀) :
    deltaDivisionRawPrimeQuotientEquiv D d a
      (Ideal.Quotient.mk (Ideal.span {(p : Raw)}) (Ideal.Quotient.mk J t)) =
        Ideal.Quotient.mk K t := by
  rw [deltaDivisionRawPrimeQuotientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingEquiv.trans_apply, idealThenPrincipalQuotEquiv_mk, Ideal.quotEquivOfEq_mk]

variable [Unique σ]
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
include hpA hdA haA hgL hv

/-- 概要：実 δ 関係イデアルに p を加えたイデアルは分母で飽和している。
方針：和と有向上限を交換し、一有限段の mod p の分母正則性で消去する。
規約：分母の係数像を元の自由環で扱う。
使われ方：BS Rem 7.15（著者版 p.62）の raw 包の mod p 正則性。 -/
theorem deltaDivisionUnaryRaw_primeIdeal_d_saturated (t : L₀)
    (ht : MvPolynomial.C d * t ∈ K) : t ∈ K := by
  have hK : K = ⨆ N, Ideal.span {(p : L₀)} ⊔ I N := by
    rw [deltaDivision_deltaClosure_eq_iSup_finiteRelations, sup_iSup]
  rw [hK] at ht ⊢
  have hmono : Monotone (fun N => Ideal.span {(p : L₀)} ⊔ I N) :=
    fun _ _ h => sup_le_sup_left (deltaDivisionFiniteRelationIdeal_mono D d a h) _
  obtain ⟨N, hN⟩ := (Submodule.mem_iSup_of_directed _ hmono.directed_le).mp ht
  let e := deltaDivisionFiniteStagePrimeQuotientEquiv D d a N
  have hdN := (deltaDivisionUnaryFinite_all_regular D d a hpA hdA haA hgL v hv N).2
  have hreg : IsSMulRegular (L₀ ⧸ (Ideal.span {(p : L₀)} ⊔ I N))
      (Ideal.Quotient.mk (Ideal.span {(p : L₀)} ⊔ I N) (MvPolynomial.C d)) := by
    simpa only [e, deltaDivisionFiniteStagePrimeQuotientEquiv_mk] using
      (ringEquiv_isSMulRegular e _).mp hdN
  have hz : Ideal.Quotient.mk (Ideal.span {(p : L₀)} ⊔ I N) t = 0 := by
    apply hreg
    change Ideal.Quotient.mk _ (MvPolynomial.C d) * Ideal.Quotient.mk _ t = _ * 0
    rw [mul_zero, ← map_mul]
    exact Ideal.Quotient.eq_zero_iff_mem.mpr hN
  exact (le_iSup (fun N => Ideal.span {(p : L₀)} ⊔ I N) N)
    (Ideal.Quotient.eq_zero_iff_mem.mp hz)

/-- 概要：元の一元 raw δ 包の mod p で分母は正則。
方針：和イデアルの分母飽和性を代表元に適用し、標準比較で実 mod p へ戻す。
規約：完備性を要求せず、追加のねじれ除去商も作らない。
使われ方：BS Rem 7.15（著者版 p.62）の実完備化前の正則対の第二成分。 -/
theorem deltaDivisionUnaryRaw_mod_prime_d_regular :
    IsSMulRegular (Raw ⧸ Ideal.span {(p : Raw)})
      (Ideal.Quotient.mk (Ideal.span {(p : Raw)}) (Ideal.Quotient.mk J (MvPolynomial.C d))) := by
  apply (ringEquiv_isSMulRegular (deltaDivisionRawPrimeQuotientEquiv D d a) _).mpr
  rw [deltaDivisionRawPrimeQuotientEquiv_mk]
  apply isSMulRegular_iff_right_eq_zero_of_smul.mpr
  intro x hx
  obtain ⟨t, rfl⟩ := Ideal.Quotient.mk_surjective x
  have ht : MvPolynomial.C d * t ∈ K := by
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    simpa only [map_mul, smul_eq_mul] using hx
  exact Ideal.Quotient.eq_zero_iff_mem.mpr
    (deltaDivisionUnaryRaw_primeIdeal_d_saturated D d a hpA hdA haA hgL v hv t ht)

end SerrePositivity.BhattScholze.Andre
