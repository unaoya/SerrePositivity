module

public import SerrePositivity.BhattScholze.Andre.Remark715.DeltaDivisionFiniteModPrimeRegularity
public import SerrePositivity.BhattScholze.Andre.Remark715.RegularTripleQuotientStep

/-!
# André E1・E2：有限 δ 関係商の二重剰余と標準一重商

## 概要

有限 raw 関係商の mod p、さらに mod d を、元の自由環の対応する一重商へ移す。
一元族で次関係を課す商も次の有限段と同定する。
BS Rem 7.15（著者版 p.62）の正則性の帰納法に用いる。

## 方針

通常商の第三同型定理を使い、全ての代表元の像を保持する。

## 規約

正則性・完備性を仮定しない通常環同型。

## 使われ方

次段の正則性と既存の mod(p,d) Witt 計算を同じ有限商へ移す。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre

/-- 概要：イデアル商に主関係を追加する二重商は和イデアル商と環同型。
方針：生成イデアルを像イデアルに書き換え第三同型定理を使う。
規約：元の代表元を保つ。
使われ方：BS Rem 7.15（著者版 p.62）の有限関係追加と係数商。 -/
def idealThenPrincipalQuotEquiv {R : Type u} [CommRing R] (I : Ideal R) (r : R) :
    ((R ⧸ I) ⧸ Ideal.span {Ideal.Quotient.mk I r}) ≃+* R ⧸ (I ⊔ Ideal.span {r}) :=
  (Ideal.quotEquivOfEq (show Ideal.span {Ideal.Quotient.mk I r} =
    (Ideal.span {r}).map (Ideal.Quotient.mk I) by rw [Ideal.map_span, Set.image_singleton])).trans
      (DoubleQuot.quotQuotEquivQuotSup I (Ideal.span {r}))

/-- 概要：主関係を追加する商同型は元の代表元を保つ。
方針：第三同型定理の代表元公式を使う。
規約：任意のイデアルと関係元を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の有限段の係数照合。 -/
theorem idealThenPrincipalQuotEquiv_mk {R : Type u} [CommRing R]
    (I : Ideal R) (r t : R) :
    idealThenPrincipalQuotEquiv I r (Ideal.Quotient.mk _ (Ideal.Quotient.mk I t)) =
      Ideal.Quotient.mk _ t := by
  rw [idealThenPrincipalQuotEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
  exact DoubleQuot.quotQuotEquivQuotSup_quotQuotMk I (Ideal.span {r}) t

variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (N : ℕ)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "I" => deltaDivisionFiniteRelationIdeal D d a N
local notation "B" => L₀ ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "qp" => Ideal.Quotient.mk (Ideal.span {(p : B)})
local notation "Ip" => Ideal.span {(p : L₀)} ⊔ I
local notation "Ipd" => Ideal.span {(p : L₀), MvPolynomial.C d} ⊔ I

/-- 概要：有限関係商の通常 mod p は元の自由環の (p)+I_N 商と環同型。
方針：自然数の像を照合して主関係追加の同型を使う。
規約：一重商は既存の有限 mod p 分離と同じイデアル順序にする。
使われ方：BS Rem 7.15（著者版 p.62）の次関係正則性の移送。 -/
def deltaDivisionFiniteStagePrimeQuotientEquiv : (B ⧸ Ideal.span {(p : B)}) ≃+* L₀ ⧸ Ip :=
  (Ideal.quotEquivOfEq (show Ideal.span {(p : B)} = Ideal.span {q (p : L₀)} by
    rw [map_natCast])).trans
    ((idealThenPrincipalQuotEquiv I (p : L₀)).trans (Ideal.quotEquivOfEq (sup_comm _ _)))

/-- 概要：有限段の mod p 比較は元の自由環の代表元を保つ。
方針：主関係追加同型の公式を使う。
規約：全ての自由環元 t を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の係数と次関係の照合。 -/
theorem deltaDivisionFiniteStagePrimeQuotientEquiv_mk (t : L₀) :
    deltaDivisionFiniteStagePrimeQuotientEquiv D d a N (qp (q t)) = Ideal.Quotient.mk Ip t := by
  rw [deltaDivisionFiniteStagePrimeQuotientEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, RingEquiv.trans_apply,
    idealThenPrincipalQuotEquiv_mk, Ideal.quotEquivOfEq_mk]

local notation "Ep" => deltaDivisionFiniteStagePrimeQuotientEquiv D d a N

/-- 概要：有限関係商の mod p,d 二重剰余は既存の一重 mod(p,d) 商と環同型。
方針：mod p 比較を d の商へ降ろし、和イデアルを整理する。
規約：Witt 正規化と同じ一重イデアル商を対象にする。
使われ方：BS Rem 7.15（著者版 p.62）の次関係の mod d 正則性の移送。 -/
def deltaDivisionFiniteStagePairQuotientEquiv :
    ((B ⧸ Ideal.span {(p : B)}) ⧸ Ideal.span {qp (q (MvPolynomial.C d))}) ≃+* L₀ ⧸ Ipd :=
  ((Ideal.quotientEquiv _ _ Ep (show
    Ideal.span {Ideal.Quotient.mk Ip (MvPolynomial.C d)} =
      (Ideal.span {qp (q (MvPolynomial.C d))}).map (Ep).toRingHom by
      rw [Ideal.map_span, Set.image_singleton]
      congr 1)).trans
    (idealThenPrincipalQuotEquiv Ip (MvPolynomial.C d))).trans
      (Ideal.quotEquivOfEq (show Ip ⊔ Ideal.span {MvPolynomial.C d} = Ipd by
        rw [Ideal.span_insert]
        ac_rfl))

/-- 概要：有限段の mod p,d 比較は元の自由環の代表元を保つ。
方針：商への降下と主関係追加の二つの代表元公式を使う。
規約：三つの実商射をそのまま用いる。
使われ方：BS Rem 7.15（著者版 p.62）の実 δ 関係の正則性の照合。 -/
theorem deltaDivisionFiniteStagePairQuotientEquiv_mk (t : L₀) :
    deltaDivisionFiniteStagePairQuotientEquiv D d a N (Ideal.Quotient.mk _ (qp (q t))) =
      Ideal.Quotient.mk Ipd t := by
  rw [deltaDivisionFiniteStagePairQuotientEquiv, RingEquiv.trans_apply,
    RingEquiv.trans_apply, Ideal.quotientEquiv_mk, deltaDivisionFiniteStagePrimeQuotientEquiv_mk,
    idealThenPrincipalQuotEquiv_mk, Ideal.quotEquivOfEq_mk]

variable [Unique σ]
local notation "g" => deltaDivisionIteratedRelation D d a (default : σ)

/-- 概要：一元族の深さ零の関係イデアルは初期関係の主イデアル。
方針：唯一の族添字と唯一の深さ零添字を照合する。
規約：分母 d と分子族 a は任意。
使われ方：BS Rem 7.15（著者版 p.62）の正則性帰納法の初期段。 -/
theorem deltaDivisionUnaryFiniteIdeal_zero :
    deltaDivisionFiniteRelationIdeal D d a 0 = Ideal.span {g 0} := by
  unfold deltaDivisionFiniteRelationIdeal
  congr 1
  ext z
  constructor
  · rintro ⟨⟨s, n⟩, rfl⟩
    have hs : s = (default : σ) := Subsingleton.elim _ _
    have hn : n = 0 := Fin.ext (by omega)
    subst s
    subst n
    exact Set.mem_singleton _
  · rintro rfl
    exact ⟨((default : σ), 0), rfl⟩

/-- 概要：一元族の次有限段は一つの次 δ 関係を追加して得る。
方針：既存の族の和イデアル式で唯一の添字を照合する。
規約：任意の深さ N。
使われ方：BS Rem 7.15（著者版 p.62）の正則性の次段への移送。 -/
theorem deltaDivisionUnaryFiniteIdeal_succ :
    deltaDivisionFiniteRelationIdeal D d a (N + 1) = I ⊔ Ideal.span {g (N + 1)} := by
  rw [deltaDivisionFiniteRelationIdeal_succ]
  congr 1
  congr 1
  ext z
  constructor
  · rintro ⟨s, rfl⟩
    have hs : s = (default : σ) := Subsingleton.elim _ _
    subst s
    exact Set.mem_singleton _
  · rintro rfl
    exact ⟨default, rfl⟩

/-- 概要：一元の次関係商は元の次有限段と環同型。
方針：主関係追加の同型と次段イデアルの等式を合成する。
規約：完備化を行わない通常商の同型。
使われ方：BS Rem 7.15（著者版 p.62）の正則対の帰納法。 -/
def deltaDivisionUnaryFiniteStepEquiv :
    (B ⧸ Ideal.span {q (g (N + 1))}) ≃+*
      L₀ ⧸ deltaDivisionFiniteRelationIdeal D d a (N + 1) :=
  (idealThenPrincipalQuotEquiv I (g (N + 1))).trans
    (Ideal.quotEquivOfEq (deltaDivisionUnaryFiniteIdeal_succ D d a N).symm)

/-- 概要：次有限段の比較は元の自由環の代表元を保つ。
方針：主関係追加同型の代表元公式を使う。
規約：元の自由環の全ての元を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の係数正則性の移送。 -/
theorem deltaDivisionUnaryFiniteStepEquiv_mk (t : L₀) :
    deltaDivisionUnaryFiniteStepEquiv D d a N (Ideal.Quotient.mk _ (q t)) =
      Ideal.Quotient.mk _ t := by
  rw [deltaDivisionUnaryFiniteStepEquiv, RingEquiv.trans_apply,
    idealThenPrincipalQuotEquiv_mk, Ideal.quotEquivOfEq_mk]

end SerrePositivity.BhattScholze.Andre
