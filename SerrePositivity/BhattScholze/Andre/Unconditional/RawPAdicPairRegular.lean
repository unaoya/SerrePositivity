module

public import SerrePositivity.BhattScholze.Andre.Unconditional.RawPrincipalH0Comparison

/-!
# 元の通常 p 完備化の正則対から hpR を除く

## 概要
BS Rem 7.15（著者版 p.62）の任意モニック入力について、元の通常 p 完備化で p と分母は正則。

## 方針
元の実第一完備化の H⁰ 比較で分母正則性を移し、次数零では元の分母の単元性を使う。

## 規約
元の AdicCompletion と標準係数射を保持する。raw mod p の分母正則性を仮定しない。

## 使われ方
旧 powerRootPrismMonicRaw_pAdic_regular_pair の hpR なしの置換先。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits DerivedCompletion
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] HasDerivedCategory.standard

/-- 概要：係数制限を保つ線形同型は、元の基底元の正則性を標準代数像へ移す。
方針：同じ線形同型の逆で単射性を運び、標準スカラー作用を乗法へ書き直す。
規約：基底射の単射性・平坦性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の具体的な古典的完備化の作用の照合。 -/
theorem unconditionalRegularity_of_restricted_linearEquiv
    {A R S : Type u} [CommRing A] [CommRing R] [CommRing S] [Algebra R S]
    (c : A →+* R) (M : ModuleCat.{u} A)
    (e : M ≃ₗ[A] (ModuleCat.restrictScalars c).obj (ModuleCat.of R S))
    (d : A) (hd : IsSMulRegular M d) : IsSMulRegular S (algebraMap R S (c d)) := by
  intro x y hxy
  apply e.symm.injective
  apply hd
  change d • e.symm x = d • e.symm y
  rw [← e.symm.map_smul, ← e.symm.map_smul]
  apply congrArg e.symm
  change (c d) • x = (c d) • y
  simpa only [smul_eq_mul, Algebra.smul_def] using hxy

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hpNat" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hpNat
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "Raw" => DeltaAdjoinDivision E dP a
local notation "j" => deltaAdjoinDivisionMap E dP a
local notation "c" => algebraMap A Raw
local notation "C" => AdicCompletion (Ideal.span {(p : Raw)}) Raw

/-- 概要：正次数モニック入力では元の通常 p 完備化の分母像が正則。
方針：元の実第一完備化 H⁰ の分母正則性を、標準 raw 主完備化比較で移す。
規約：hpR と raw mod p の分母正則性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の元の通常 p 完備化の正則対。 -/
theorem powerRootPrismMonicRaw_pAdic_generator_regular_of_positive_unconditional
    (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    IsSMulRegular C (algebraMap Raw C (j dP)) := by
  let := principalCompletionCommRing Raw (p : Raw)
  let := principalCompletionAlgebra Raw (p : Raw)
  have hpRaw : IsSMulRegular Raw (p : Raw) :=
    powerRootPrismMonicRaw_p_mul_injective_of_unconditional W hW f hf
  let eC := (principalCompletionAdicAlgEquiv Raw (p : Raw) hpRaw).toLinearEquiv.toModuleIso
  let e := (powerRootPrismMonicSourcePrincipalH0Iso_of_unconditional W hW f ≪≫
    (ModuleCat.restrictScalars c).mapIso eC).toLinearEquiv
  have hsrc := powerRootPrismMonicSourcePCompletion_generator_injective_of_positive_unconditional
    W hW f hf hdeg
  exact unconditionalRegularity_of_restricted_linearEquiv c _ e W.generator hsrc

/-- 概要：任意モニック入力では元の通常 p 完備化の分母像が正則。
方針：正次数の実第一完備化計算と、f=1 の場合の元の分母の単元性を合流する。
規約：旧主張のモニック性だけを保持し、hpR を除く。
使われ方：BS Rem 7.15（著者版 p.62）の元の通常 p 完備化の正則対。 -/
theorem powerRootPrismMonicRaw_pAdic_generator_regular_of_unconditional (hf : f.Monic) :
    IsSMulRegular C (algebraMap Raw C (j dP)) := by
  by_cases hz : f.natDegree = 0
  · have hf1 : f = 1 := Polynomial.eq_one_of_monic_natDegree_zero hf hz
    have ha : ∃ s, a s = 1 := by
      refine ⟨(PUnit.unit : PUnit.{u + 1}), ?_⟩
      simp only [powerRootPrismMonicUnaryFamily, powerRootMonicPDInput, hf1, map_one]
    exact ((unconditionalRaw_denominator_isUnit_of_unit_numerator E dP a ha).map
      (algebraMap Raw C)).mul_right_injective
  · exact powerRootPrismMonicRaw_pAdic_generator_regular_of_positive_unconditional
      W hW f hf (Nat.pos_of_ne_zero hz)

/-- 概要：元の通常 p 完備化で p と分母はともに正則。
方針：元の raw p 正則性の完備化保存と、元の実源から移した分母正則性を合流する。
規約：旧公開定理と同じ対象・標準射で hpR だけを除く。正次数は不要。
使われ方：BS Rem 7.15（著者版 p.62）の元の実二座標完備化への入力。 -/
theorem powerRootPrismMonicRaw_pAdic_regular_pair_of_unconditional (hf : f.Monic) :
    let CP := AdicCompletion (Ideal.span {(p : Raw)}) Raw
    IsSMulRegular CP (p : CP) ∧ IsSMulRegular CP (algebraMap Raw CP (j dP)) := by
  exact ⟨powerRootPrismMonicRaw_pAdic_prime_regular_of_unconditional W hW f hf,
    powerRootPrismMonicRaw_pAdic_generator_regular_of_unconditional W hW f hf⟩

end SerrePositivity.BhattScholze.Andre
