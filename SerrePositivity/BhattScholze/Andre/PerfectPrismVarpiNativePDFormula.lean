module

public import SerrePositivity.BhattScholze.Andre.PerfectPrismVarpiNativePDFlat
public import SerrePositivity.BhattScholze.Andre.Unconditional.MonicPDEnvelope

/-!
# André E1・E2：原典係数上の実分冪値と切断変数

## 概要

無限根モニック pd 包の p 冪次分冪は、切断表示の対応する変数へ写る。
BS Rem 7.15(1)（著者版 p.62）の gᵢ の明示的な同定。

## 方針

無条件版の実分冪値の公式と、切断表示の標準生成元の公式を合わせる。
原典とは異なる射影的係数商からの分冪構造を使う。

## 規約

モニック性だけを要求し、prism 商の p 正則性と正次数を要求しない。

## 使われ方

旧 hpR 付き公開公式と同じ係数作用・切断表示・添字を保って置換する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "R₀" => A ⧸ Ideal.span {(p : A)}
local notation "Rv" => (A ⧸ W.ideal) ⧸ Ideal.span {perfectPrismVarpi W hW}
local notation "Nv" => PowerRootPolynomial Rv p hp
local notation "barr" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {perfectPrismVarpi W hW}))
  (Ideal.Quotient.mk (OrientedPrism.ideal W))
local notation "zv" f => powerRootPolynomialBaseMap Rv p hp (Polynomial.map barr f)
local notation "Dv" f => PrincipalDPPresentation Nv (zv f)

/-- 概要：実 pd 包の素数冪分冪は切断表示の対応する変数へ写る。
方針：実分冪の標準値を使い、素数冪標準生成元の表示公式を適用する。
規約：g₁ を添字零の変数とし、次数は p^(i+1)。
使われ方：BS Rem 7.15(1)（著者版 p.62）の gᵢ と分冪値の具体的な対応。 -/
theorem perfectPrismVarpiNativePDEnvelope_truncated_dpow
    (f : Polynomial A) (hf : f.Monic)
    (i : ℕ) :
    let := principalDPQuotientAlgebra hp (perfectPrismVarpiRootRing_prime_eq_zero W hW) (zv f)
    perfectPrismVarpiNativePDEnvelope_truncatedEquiv W hW f
      ((perfectPrismVarpiNativeDividedPowers_of_unconditional W hW f hf).dpow (p ^ (i + 1))
        (algebraMap Nv (Dv f) (zv f))) = Ideal.Quotient.mk _ (MvPolynomial.X i) := by
  let := principalDPQuotientAlgebra hp (perfectPrismVarpiRootRing_prime_eq_zero W hW) (zv f)
  rw [perfectPrismVarpiNativeDividedPowers_base_apply_of_unconditional]
  change principalDPTruncatedEquiv p (perfectPrismVarpiRootRing_prime_eq_zero W hW) (zv f)
    (principalDPGenerator (zv f) (p ^ (i + 1))) = _
  exact principalDPTruncatedEquiv_generator_succ p
    (perfectPrismVarpiRootRing_prime_eq_zero W hW) (zv f) i

end SerrePositivity.BhattScholze.Andre
