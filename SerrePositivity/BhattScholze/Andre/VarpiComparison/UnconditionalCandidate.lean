module

public import SerrePositivity.BhattScholze.Andre.VarpiComparison.Candidate
public import SerrePositivity.BhattScholze.Andre.VarpiComparison.UnconditionalPD
public import SerrePositivity.BhattScholze.Andre.Unconditional.PowerRootHodgeTateReduction
public import SerrePositivity.BhattScholze.Andre.Unconditional.PrimeReductionPurity

/-!
# BS Rem 7.15（著者版 p.62）：無条件の Hodge–Tate 係数比較

## 概要
元の候補 T の p 完全忠実平坦性と自然な ϖ 商の忠実平坦性を照合する。

## 方針
正次数では実際の導来 p 還元の次数零集中を用い、次数零では源 H の零環性を用いる。

## 規約
一般の通常商による判定には加群上の正則性が必要である。
この具体的候補では無条件の導来還元定理を使い、T 上の正則性を仮定しない。
f'=φ_A⁻¹(f) と既存の係数作用を保持する。旧名は削除しない。

## 使われ方
A1-c2 の公開比較を hpR なしで供給する。
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

/-- 概要：元の候補の p 完全忠実平坦性は自然な ϖ 商の忠実平坦性と同値。
方針：正次数では無条件の導来還元を使い、次数零では源の零環性から平坦性を得る。
規約：モニック性のみを仮定し、hpR と余分な正次数仮定を置かない。
使われ方：BS Rem 7.15（著者版 p.62）の二つの係数表記の照合。 -/
theorem hodgeTate_completelyFaithfullyFlat_iff_of_unconditional (hf : f.Monic) :
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
    by_cases hz : f.natDegree = 0
    · let : Subsingleton H :=
        powerRootPrismMonic_pdCompletion_subsingleton_of_natDegree_zero W hW f hf hz
      have hCF : IsCompletelyFlat (Ideal.span {v}) T := by
        intro N _ _ _
        apply (isConcentratedInDegreeZero_derivedTensor_iff T N).mpr
        intro i hi
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hi)
        exact torModule_subsingleton_of_flat T N j
      have := hTv
      have hTensor := Module.FaithfullyFlat.of_linearEquiv Rv Tv
        (Algebra.TensorProduct.quotIdealMapEquivQuotTensor T (Ideal.span {v})).symm.toLinearEquiv
      exact (completelyFaithfullyFlat_iff v (p : R) p hp
        (perfectPrismVarpi_span_pow W hW) T).mpr ⟨hCF, hTensor⟩
    · exact powerRootPrismMonicHodgeTate_prime_completelyFaithfullyFlat_of_unconditional
        W hW f hf (Nat.pos_of_ne_zero hz)

/-- 概要：候補の p 完全忠実平坦性、自然 ϖ 剰余の忠実平坦性、f'ᵖ 商上の自由性、
実装の係数 pd 包の R/ϖ 底変換との同型を一つに集約する。
方針：pd 基底計算を自然商へ移し、無条件版の同値で p 完全忠実平坦性を得る。
規約：f'=φ_A⁻¹(f) を保持し、原典の Frobenius 引戻しを省略しない。
使われ方：BS Rem 7.15（著者版 p.62）と E1.25・E1.55・E1.56 の公開照合定理。 -/
theorem hodgeTate_coefficient_comparison_of_unconditional
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
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
  have hiff := hodgeTate_completelyFaithfullyFlat_iff_of_unconditional W hW f hf
  have hFF := powerRootPrismMonicHodgeTateVarpi_faithfullyFlat W hW f hf hdeg
  exact ⟨hiff, hodgeTateVarpi_free_over_powerQuotient W hW f hf, hFF, hiff.mpr hFF,
    ⟨(perfectPrismPDTensorVarpiEquiv W hW f').trans
      (hodgeTateVarpiPDAlgEquiv W hW f hf).symm.toRingEquiv⟩⟩

end SerrePositivity.BhattScholze.Andre.VarpiComparison
