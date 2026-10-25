module

public import SerrePositivity.BhattScholze.Andre.Remark715.DeltaDivisionFinitePrimeQuotients
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaDivisionFirstJetResidueRegular
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.Division.DeltaDivisionFiniteJetRegularity

/-!
# André E1・E2：有限 δ 関係商の p,d 正則性を次段へ保つ

## 概要

一元 raw 包の有限段で p が正則、mod p で d が正則なら、次段でも両条件が成り立つ。
BS Rem 7.15（著者版 p.62）の源の p 正則性の帰納法。

## 方針

最高係数の正則性で次関係は mod p で正則。
既存 Witt 計算で mod(p,d) でも正則なので、正則対の順序交換を二度使う。

## 規約

源の p 正則性、自由 δ 環の ghost 単射性、δ(d) の単元性を明示する。
初期段の正則性を仮定する次段の定理であり、全有限段への帰納法は別工程。

## 使われ方

無限根モニック入力の初期正則対を全有限 δ 関係商へ移す。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A] [Unique σ]
variable (D : DeltaStructure p A) (hpA : Function.Injective (fun r : A => (p : A) * r))
variable (hgL : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (d : A) (a : σ → A) (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "I" => deltaDivisionFiniteRelationIdeal D d a N
local notation "B" => L₀ ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "qp" => Ideal.Quotient.mk (Ideal.span {(p : B)})
local notation "dN" => q (MvPolynomial.C d)
local notation "g" => deltaDivisionIteratedRelation D d a (default : σ) (N + 1)
local notation "gN" => q g
local notation "Ip" => Ideal.span {(p : L₀)} ⊔ I
local notation "Ipd" => Ideal.span {(p : L₀), MvPolynomial.C d} ⊔ I
local notation "I'" => deltaDivisionFiniteRelationIdeal D d a (N + 1)
local notation "B'" => L₀ ⧸ I'
local notation "q'" => Ideal.Quotient.mk I'

include hpA hgL hv in
/-- 概要：有限段の次関係は mod p,d の通常二重商上で正則。
方針：最初の δ 関係とそれ以降の既存 Witt 正則性を場合分けして移す。
規約：前段の p,d 正則性はこの mod(p,d) 計算には不要。
使われ方：BS Rem 7.15（著者版 p.62）の正則対の次段への移送。 -/
theorem deltaDivisionUnaryFinite_next_mod_pair_regular :
    IsSMulRegular ((B ⧸ Ideal.span {(p : B)}) ⧸ Ideal.span {qp dN})
      (Ideal.Quotient.mk (Ideal.span {qp dN}) (qp gN)) := by
  have hr : IsSMulRegular (L₀ ⧸ Ipd) (Ideal.Quotient.mk Ipd g) := by
    cases N with
    | zero => exact deltaDivisionFirstJet_residue_isSMulRegular D d a v hv default
    | succ n =>
      have hpL : Function.Injective (fun r : L₀ => (p : L₀) * r) := by
        simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
          (show IsSMulRegular A (p : A) from hpA).of_flat (S := L₀)
      exact deltaDivisionFiniteNextJet_quotient_isSMulRegular D hpA hpL hgL d a v hv n default
  let e := deltaDivisionFiniteStagePairQuotientEquiv D d a N
  apply (ringEquiv_isSMulRegular e _).mpr
  rw [deltaDivisionFiniteStagePairQuotientEquiv_mk]
  exact hr

/-- 概要：d が有限段の mod p で正則なら次関係も同じ mod p で正則。
方針：一重商で証明した次関係の正則性を標準 mod p 商同型で戻す。
規約：d の正則性を次段帰納法の入力とする。
使われ方：BS Rem 7.15（著者版 p.62）の p 正則性の保存。 -/
theorem deltaDivisionUnaryFinite_next_mod_prime_regular
    (hd : IsSMulRegular (B ⧸ Ideal.span {(p : B)}) (qp dN)) :
    IsSMulRegular (B ⧸ Ideal.span {(p : B)}) (qp gN) := by
  let e := deltaDivisionFiniteStagePrimeQuotientEquiv D d a N
  have hd' := (ringEquiv_isSMulRegular e (qp dN)).mp hd
  rw [deltaDivisionFiniteStagePrimeQuotientEquiv_mk] at hd'
  have hr := deltaDivisionFiniteModPrime_next_regular D d a N hd' default
  apply (ringEquiv_isSMulRegular e _).mpr
  rw [deltaDivisionFiniteStagePrimeQuotientEquiv_mk]
  exact hr

include hpA hgL hv in
/-- 概要：一元有限関係商の p 正則性と mod p の d 正則性は次段へ保存される。
方針：次関係の mod p と mod(p,d) 正則性で三元の正則性保存を使う。
規約：前段の二つの正則性は明示仮定。
使われ方：BS Rem 7.15（著者版 p.62）の全有限段への同時帰納法。 -/
theorem deltaDivisionUnaryFinite_step_regular
    (hpN : IsSMulRegular B (p : B))
    (hdN : IsSMulRegular (B ⧸ Ideal.span {(p : B)}) (qp dN)) :
    IsSMulRegular B' (p : B') ∧
      IsSMulRegular (B' ⧸ Ideal.span {(p : B')})
        (Ideal.Quotient.mk (Ideal.span {(p : B')}) (q' (MvPolynomial.C d))) := by
  have hgN := deltaDivisionUnaryFinite_next_mod_prime_regular D d a N hdN
  have hgdN := deltaDivisionUnaryFinite_next_mod_pair_regular D hpA hgL d a v hv N
  have hstep := regularTripleQuotientStep (p : B) dN gN hpN hdN hgN hgdN
  let e := deltaDivisionUnaryFiniteStepEquiv D d a N
  have hpQ : IsSMulRegular (B ⧸ Ideal.span {gN}) (p : B ⧸ Ideal.span {gN}) := by
    simpa only [map_natCast] using hstep.1
  have hdQ : IsSMulRegular ((B ⧸ Ideal.span {gN}) ⧸
      Ideal.span {(p : B ⧸ Ideal.span {gN})})
      (Ideal.Quotient.mk (Ideal.span {(p : B ⧸ Ideal.span {gN})})
        (Ideal.Quotient.mk (Ideal.span {gN}) dN)) := by
    let C := B ⧸ Ideal.span {gN}
    let j : B →+* C := Ideal.Quotient.mk _
    have aux (c : C) (hc : c = (p : C))
        (hr : IsSMulRegular (C ⧸ Ideal.span {c})
          (Ideal.Quotient.mk (Ideal.span {c}) (j dN))) :
        IsSMulRegular (C ⧸ Ideal.span {(p : C)})
          (Ideal.Quotient.mk (Ideal.span {(p : C)}) (j dN)) := by
      subst c
      exact hr
    exact aux _ (map_natCast j p) hstep.2
  refine ⟨?_, ?_⟩
  · have h := (ringEquiv_isSMulRegular e (p : B ⧸ Ideal.span {gN})).mp hpQ
    simpa only [map_natCast] using h
  · let ep : ((B ⧸ Ideal.span {gN}) ⧸ Ideal.span {(p : B ⧸ Ideal.span {gN})}) ≃+*
        (B' ⧸ Ideal.span {(p : B')}) :=
      Ideal.quotientEquiv _ _ e (by rw [Ideal.map_span, Set.image_singleton, map_natCast])
    have h := (ringEquiv_isSMulRegular ep _).mp hdQ
    have he : ep (Ideal.Quotient.mk _ (Ideal.Quotient.mk _ dN)) =
        Ideal.Quotient.mk (Ideal.span {(p : B')}) (q' (MvPolynomial.C d)) := by
      rw [Ideal.quotientEquiv_mk, deltaDivisionUnaryFiniteStepEquiv_mk]
    rw [he] at h
    exact h

end SerrePositivity.BhattScholze.Andre
