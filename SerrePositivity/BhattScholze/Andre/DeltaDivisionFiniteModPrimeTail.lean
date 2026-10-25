module

public import SerrePositivity.BhattScholze.RootedExtension.Division.DeltaDivisionFiniteRelationsRegular

/-!
# André E1・E2：有限 δ 関係商の mod p と最高変数の正則性

## 概要

有限 raw δ 関係商を mod p で初期係数商と後続変数へ分離する。
そこで d が正則なら次の δ 関係も正則となる。
BS Rem 7.15（著者版 p.62）の源の p 正則性に向けた有限段の計算。

## 方針

p を初期変数環のイデアルへ含めて既存の変数分離を使う。
次関係の先頭係数 φ^(N+1)(d) は mod p で d^(p^(N+1)) となる。

## 規約

全有限段の正則性を結論する段階ではなく、帰納法の次段を供給する。
prismatic 完備化や原典の T との同定は別工程。

## 使われ方

有限商の p 正則性と mod p の d 正則性の同時帰納法。
-/

@[expose] public noncomputable section
universe u v
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A] {σ : Type v}
variable (D : DeltaStructure p A) (d : A) (a : σ → A) (N : ℕ)
local notation "L₀" => RelativeFreeDeltaRing (R := A) σ
local notation "I₀" => deltaDivisionFiniteRelationIdeal D d a N
local notation "B₀" => MvPolynomial (σ × Fin (N + 1)) A
local notation "J₀" => deltaDivisionFiniteStageInitialIdeal D d a N
local notation "Jp" => Ideal.span {(p : B₀)} ⊔ J₀
local notation "Ip" => Ideal.span {(p : L₀)} ⊔ I₀

/-- 概要：初期有限関係と p のイデアルの拡張は全自由環の同じイデアル。
方針：既存の初期関係の像と環射の自然数保存を使う。
規約：添字型の有限性は仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の有限 mod p 商の分離。 -/
theorem deltaDivisionFiniteModPrimeInitialIdeal_map :
    (Jp).map (relativeFreeFiniteInitialPolynomialMap (N + 1) σ A).toRingHom = Ip := by
  rw [Ideal.map_sup, deltaDivisionFiniteStageInitialIdeal_map,
    Ideal.map_span, Set.image_singleton, map_natCast]

/-- 概要：有限関係商の mod p は初期 mod p 商上の後続多項式環と環同型。
方針：初期イデアルの像を照合して既存の任意初期商比較を適用する。
規約：一重イデアル商として mod p を表す。
使われ方：BS Rem 7.15（著者版 p.62）の次関係の先頭係数計算。 -/
def deltaDivisionFiniteModPrimeTailEquiv :
    (L₀ ⧸ Ip) ≃+* MvPolynomial (σ × ℕ) (B₀ ⧸ Jp) :=
  (Ideal.quotEquivOfEq (deltaDivisionFiniteModPrimeInitialIdeal_map D d a N).symm).trans
    (relativeFreeFiniteInitialQuotientEquiv (N + 1) Jp)

/-- 概要：有限 mod p 分離同型の代表元公式。
方針：初期商比較の代表元公式を使う。
規約：全自由環の全ての元を含める。
使われ方：BS Rem 7.15（著者版 p.62）の係数と次関係の照合。 -/
theorem deltaDivisionFiniteModPrimeTailEquiv_mk (f : L₀) :
    deltaDivisionFiniteModPrimeTailEquiv D d a N (Ideal.Quotient.mk Ip f) =
      MvPolynomial.map (Ideal.Quotient.mk Jp)
        (relativeFreeFiniteVariableSplitAlgEquiv (N + 1) σ A f) := by
  rw [deltaDivisionFiniteModPrimeTailEquiv, RingEquiv.trans_apply,
    Ideal.quotEquivOfEq_mk, relativeFreeFiniteInitialQuotientEquiv_mk]

/-- 概要：有限 mod p 分離同型は元の A 係数を初期係数商へ送る。
方針：変数分離と多項式写像の係数公式を使う。
規約：元の標準係数射を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の d 正則性の降下。 -/
theorem deltaDivisionFiniteModPrimeTailEquiv_coeff (r : A) :
    deltaDivisionFiniteModPrimeTailEquiv D d a N (Ideal.Quotient.mk Ip (MvPolynomial.C r)) =
      MvPolynomial.C (Ideal.Quotient.mk Jp (MvPolynomial.C r)) := by
  rw [deltaDivisionFiniteModPrimeTailEquiv_mk,
    relativeFreeFiniteVariableSplitAlgEquiv_C, MvPolynomial.map_C]

/-- 概要：次の δ 関係は有限 mod p 分離後も最高変数の一次式。
方針：既存の先頭項と下位項の分解を通常商へ送る。
規約：最高係数を φ^(N+1)(d) の像のまま表示する。
使われ方：BS Rem 7.15（著者版 p.62）の次関係の正則性。 -/
theorem deltaDivisionFiniteModPrimeTailEquiv_next (s : σ) :
    deltaDivisionFiniteModPrimeTailEquiv D d a N
      (Ideal.Quotient.mk Ip (deltaDivisionIteratedRelation D d a s (N + 1))) =
        MvPolynomial.C (Ideal.Quotient.mk Jp (MvPolynomial.C (D.frobeniusLift^[N + 1] d))) *
          MvPolynomial.X (s, 0) +
        MvPolynomial.C (Ideal.Quotient.mk Jp
          (deltaDivisionFiniteLeadingLowerPolynomial D d a s (N + 1))) := by
  rw [deltaDivisionFiniteModPrimeTailEquiv_mk,
    deltaDivisionIteratedRelation_eq_leading_add_lower]
  have hx := relativeFreeFiniteVariableSplitAlgEquiv_X_tail (N + 1) σ A s 0
  simp only [zero_add] at hx
  rw [map_add, map_mul, relativeFreeFiniteVariableSplitAlgEquiv_C, hx,
    relativeFreeFiniteVariableSplitAlgEquiv_initial, map_add, map_mul,
    MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.map_C]

end SerrePositivity.BhattScholze.Andre
