module

public import SerrePositivity.BhattScholze.Andre.VarpiComparison.Flatness
public import SerrePositivity.BhattScholze.Andre.VarpiComparison.PDBaseChange
public import SerrePositivity.BhattScholze.Andre.PowerRootPrismMonicHodgeTateCompletelyFlat

/-!
# BS Rem 7.15（著者版 p.62）：具体的候補の係数表記の照合

## 概要
元の自然な Hodge–Tate 候補 T について、p 完全忠実平坦性と R/ϖ 上の
通常忠実平坦性を結び、同じ剰余の pd 底変換表示と fᵖ 商上の自由性を同時に公開する。

## 方針
自然な係数作用を保つ既存の代数同型により、pd 包の基底計算を実際の T/ϖ へ移す。

## 規約
既存の候補比較に現れる入力は f'=φ_A⁻¹(f) である。原典の φ_A 引戻しを省略して
元の f と同一視しない。prism 商の p 正則性とモニック性・正次数を明示する。

## 使われ方
E1.25・E1.55・E1.56 と原典の係数表記を照合する補足であり、主定理の引用には触れない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre.VarpiComparison
open SerrePositivity.DerivedCompletion
open scoped TensorProduct
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

/-- 概要：自然な候補の ϖ 商は同じ R/ϖ 上の pd 表示環と代数同型。
方針：既存の自然二重商比較と pd 剰余比較を合成する。
規約：入力は明示的な逆 Frobenius 係数変更 f'。
使われ方：BS Rem 7.15（著者版 p.62）の自由性と忠実平坦性の同じ候補への移送。 -/
def hodgeTateVarpiPDAlgEquiv (hf : f.Monic) :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateAlgebra W hW f
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    Tv ≃ₐ[Rv] Dv := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateAlgebra W hW f
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := powerRootPrismMonicHodgeTatePDResidueAlgebra W hW f hf
  let e := powerRootPrismMonicHodgeTateVarpiMapQuotAlgEquiv W hW f hf
  let ePD := powerRootPrismMonicVarpiResidueAlgEquiv W hW f hf
  exact e.trans ePD

/-- 概要：候補の ϖ 商に入力の p 乗商の係数作用を与える。
方針：pd 表示環の標準作用を自然剰余との同型で戻す。
規約：R/ϖ 作用は既存の自然な作用を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の fᵖ 商上の自由性の型。 -/
@[instance_reducible] def hodgeTateVarpiPowerQuotientAlgebra (hf : f.Monic) :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateAlgebra W hW f
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    Algebra Qv Tv := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateAlgebra W hW f
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := principalDPQuotientAlgebra hp hpv zv
  exact ((hodgeTateVarpiPDAlgEquiv W hW f hf).symm.toRingHom.comp (algebraMap Qv Dv)).toAlgebra

set_option maxHeartbeats 2000000 in
-- 実完備化の二重商と移送した係数作用の同一性を展開するために必要。
/-- 概要：実際の T/ϖ は原典型の無限根入力の p 乗商上自由。
方針：切断分冪表示による既存の基底を係数作用と共に戻す。
規約：モニック性は候補比較に必要で、正次数と hpR はこの自由性には不要。
使われ方：BS Rem 7.15（著者版 p.62）の自由性の文と同じ実対象の対応。 -/
theorem hodgeTateVarpi_free_over_powerQuotient (hf : f.Monic) :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateAlgebra W hW f
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    let := hodgeTateVarpiPowerQuotientAlgebra W hW f hf
    Module.Free Qv Tv := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateAlgebra W hW f
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := hodgeTateVarpiPowerQuotientAlgebra W hW f hf
  let := principalDPQuotientAlgebra hp hpv zv
  let e : Tv ≃ₐ[Qv] Dv :=
    { (hodgeTateVarpiPDAlgEquiv W hW f hf).toRingEquiv with
      commutes' := fun r => (hodgeTateVarpiPDAlgEquiv W hW f hf).apply_symm_apply _ }
  let := perfectPrismVarpiNativePDEnvelope_free_over_powerQuotient W hW f'
  exact Module.Free.of_equiv e.symm.toLinearEquiv

/-- 概要：候補の p 完全忠実平坦性は、自然な通常 ϖ 商の忠実平坦性と同値。
方針：基底・候補の ϖ 正則性を供給して一般の判定を使う。
規約：元の候補・基底射を固定し、hpR を明示する。
使われ方：BS Rem 7.15（著者版 p.62）の p 係数と ϖ 係数の照合。 -/
theorem hodgeTate_completelyFaithfullyFlat_iff
    (hpR : IsSMulRegular R (p : R)) (hf : f.Monic) :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateAlgebra W hW f
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T ↔ Module.FaithfullyFlat Rv Tv := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateAlgebra W hW f
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  constructor
  · intro hT
    exact algebraQuotient_faithfullyFlat v (p : R) p hp (perfectPrismVarpi_span_pow W hW) T hT
  · intro hTv
    have := hTv
    have hTensor := Module.FaithfullyFlat.of_linearEquiv Rv Tv
      (Algebra.TensorProduct.quotIdealMapEquivQuotTensor T (Ideal.span {v})).symm.toLinearEquiv
    have hvR := regular_of_span_power_eq v (p : R) p hp (perfectPrismVarpi_span_pow W hW) hpR
    have hV := isCompletelyFaithfullyFlat_principal_of_regular v hvR T
      (powerRootPrismMonicHodgeTate_varpi_regular W hW hpR f hf) hTensor
    exact (completelyFaithfullyFlat_iff v (p : R) p hp (perfectPrismVarpi_span_pow W hW) T).mpr hV

/-- 概要：候補の p 完全忠実平坦性、自然 ϖ 剰余の忠実平坦性、f'ᵖ 商上の自由性、
実装の係数 pd 包の R/ϖ 底変換との同型を一つに集約する。
方針：pd 基底計算を自然商へ移し、正則性付き同値の逆方向で p 完全忠実平坦性を得る。
規約：f'=φ_A⁻¹(f) を保持し、原典の Frobenius 引戻しを省略しない。
使われ方：BS Rem 7.15（著者版 p.62）と E1.25・E1.55・E1.56 の公開照合定理。 -/
theorem hodgeTate_coefficient_comparison
    (hpR : IsSMulRegular R (p : R)) (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateAlgebra W hW f
    let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
    let := hodgeTateVarpiPowerQuotientAlgebra W hW f hf
    let := varpiCoefficientAlgebra W hW
    (IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T ↔ Module.FaithfullyFlat Rv Tv) ∧
      Module.Free Qv Tv ∧ Module.FaithfullyFlat Rv Tv ∧
      IsCompletelyFaithfullyFlat (Ideal.span {(p : R)}) T ∧
      Nonempty (Rv ⊗[A ⧸ Ideal.span {(p : A)}] PowerRootCoefficientPDEnvelope p f' ≃+* Tv) := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateAlgebra W hW f
  let := powerRootPrismMonicHodgeTateVarpiAlgebra W hW f
  let := hodgeTateVarpiPowerQuotientAlgebra W hW f hf
  let := varpiCoefficientAlgebra W hW
  have hiff := hodgeTate_completelyFaithfullyFlat_iff W hW f hpR hf
  have hFF := powerRootPrismMonicHodgeTateVarpi_faithfullyFlat W hW f hf hdeg
  exact ⟨hiff, hodgeTateVarpi_free_over_powerQuotient W hW f hf, hFF, hiff.mpr hFF,
    ⟨(perfectPrismPDTensorVarpiEquiv W hW f').trans
      (hodgeTateVarpiPDAlgEquiv W hW f hf).symm.toRingEquiv⟩⟩

end SerrePositivity.BhattScholze.Andre.VarpiComparison
