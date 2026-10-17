module

public import SerrePositivity.BhattScholze.Andre.VarpiComparison.UnconditionalCandidate
public import SerrePositivity.BhattScholze.Andre.Unoriented

/-!
# André E1・E2：元の初期源と原典の係数計算の合流

## 概要

完全 prism 上の正次数モニック入力について、元の源の向きなし初期性と、
自然な Hodge–Tate 商の p 完全忠実平坦性・ϖ 剰余の pd 表示と自由性を同時に得る。
BS Rem 7.15(1)（著者版 p.62）の同じ源の係数計算。

## 方針

A1-a・A1-f の初期性、A1-b の実源の純性、A1-c の自然な係数比較を合流する。
通常剰余からの逆向きには元の源の証明済み完全忠実平坦性を使う。
原典の p ねじれなしへの帰着とは異なる純性・圏同値による経路。

## 規約

hpR・正則性・有界性を追加仮定に残さない。元の H と標準係数作用を保持する。
ϖ 剰余の入力は逆 Frobenius 係数変更 f' であり、元の f と同一視しない。
向きなし初期性は固定完全基底上の J=(d)B を満たす入力圏について述べる。

## 使われ方

原典の prismatic 源の普遍性と係数の自由性を同じ実対象について参照する公開入口。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
open scoped TensorProduct
open VarpiComparison
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => DeltaAdjoinDivision E dP a
local notation "jL" => deltaAdjoinDivisionMap E dP a
local notation "H" => PDCompletionH0 L p (jL dP)
local notation "uL" => pdCompletionUnit L p (jL dP)
local notation "T" => H ⧸ Ideal.span {uL (jL dP)}
local notation "R" => A ⧸ W.ideal
local notation "v" => perfectPrismVarpi W hW
local notation "Rv" => R ⧸ Ideal.span {v}
local notation "φ" => powerRootPrismMonicHodgeTateBaseMap W hW f
local notation "Tv" => T ⧸ Ideal.map φ (Ideal.span {v})
local notation "Nv" => PowerRootPolynomial Rv p hp
local notation "barr" => RingHom.comp
  (Ideal.Quotient.mk (Ideal.span {v})) (Ideal.Quotient.mk W.ideal)
local notation "f'" => perfectPrismInverseFrobeniusPolynomial W hW f
local notation "zv" => powerRootPolynomialBaseMap Rv p hp
  (Polynomial.map barr (perfectPrismInverseFrobeniusPolynomial W hW f))
local notation "Dv" => PrincipalDPPresentation Nv zv
local notation "Qv" => Nv ⧸ Ideal.span {zv ^ p}
local notation "hpv" => perfectPrismVarpiRootRing_prime_eq_zero W hW


/-- 概要：元の向きなし初期源について、同じ商の pd 係数比較と忠実平坦性が成立する。
方針：既存の初期性の実証人と無条件な候補比較を同じ H のまま合流する。
規約：固定基底上の入力圏と正次数モニック性を保持し、追加仮定を要求しない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の初期源と係数計算の一括参照。 -/
theorem powerRootPrismMonicSource_initial_and_coefficient_comparison
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateAlgebra W hW f
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    let := hodgeTateVarpiPowerQuotientAlgebra W hW f hf
    let := varpiCoefficientAlgebra W hW
    Nonempty (CategoryTheory.Limits.IsInitial
      (powerRootPrismMonicSourceInputObjectOfMonicPositive_unoriented W hW f hf hdeg)) ∧
      (IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T ↔ Module.FaithfullyFlat Rv Tv) ∧
      Module.Free Qv Tv ∧ Module.FaithfullyFlat Rv Tv ∧
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T ∧
      Nonempty (Rv ⊗[A ⧸ Ideal.span {(p : A)}] PowerRootCoefficientPDEnvelope p f' ≃+* Tv) := by
  exact ⟨⟨powerRootPrismMonicSourceInput_isInitialOfMonicPositive_unoriented W hW f hf hdeg⟩,
    hodgeTate_coefficient_comparison_of_unconditional W hW f hf hdeg⟩

end SerrePositivity.BhattScholze.Andre
