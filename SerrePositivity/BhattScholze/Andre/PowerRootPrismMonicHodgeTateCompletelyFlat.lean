module

public import SerrePositivity.BhattScholze.Andre.PowerRootPrismMonicHodgeTateVarpiFlat
public import SerrePositivity.CommutativeAlgebra.CompletelyFlatPowerTorsion

/-!
# André E1・E2：無限根モニック Hodge–Tate 候補の完全平坦性

## 概要

prism 商が p 正則なら、正次数モニック入力の自然な Hodge–Tate 候補は ϖ 完全忠実平坦で、
p 完全平坦。BS Rem 7.15（著者版 p.62）の具体的候補の平坦性。

## 方針

(ϖ^p)=(p) と p 正則性から基底と候補の ϖ 正則性を得る。
自然な ϖ 剰余の忠実平坦性を正則主元判定へ渡し、冪ねじれの Tor 消滅で p へ移す。

## 規約

元の実完備化と基底射を保持する。prismatic 源との同定は別工程。

## 使われ方

通常 p 剰余の忠実性と合わせた p 完全忠実平坦性への入力。
-/

@[expose] public noncomputable section
universe u
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion

/-- 概要：正則元と同じ主イデアルを生成する正冪の底も正則。
方針：主イデアル所属による可除性と積・正冪の正則性を使う。
規約：零環も含める。
使われ方：BS Rem 7.15（著者版 p.62）の (ϖ^p)=(p) からの正則性。 -/
theorem regular_of_span_power_eq {B : Type u} [CommRing B] (b c : B) (n : ℕ)
    (hn : 0 < n) (he : Ideal.span {b ^ n} = Ideal.span {c}) (hc : IsSMulRegular B c) :
    IsSMulRegular B b := by
  have hm : c ∈ Ideal.span {b ^ n} := by rw [he]; exact Ideal.mem_span_singleton_self c
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton.mp hm
  rw [hz, mul_comm] at hc
  exact (IsSMulRegular.pow_iff hn).mp hc.of_mul

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect)
variable (hpR : IsSMulRegular (A ⧸ W.ideal) (p : A ⧸ W.ideal))
variable (f : Polynomial A) (hf : f.Monic) (hdeg : 0 < f.natDegree)
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
local notation "φ" => powerRootPrismMonicHodgeTateBaseMap W hW f

include hpR hf in
/-- 概要：自然な Hodge–Tate 候補で基底の ϖ は正則に作用する。
方針：基底の主イデアル等式を自然な基底射で移し、候補の p 正則性を使う。
規約：正次数は不要。
使われ方：BS Rem 7.15（著者版 p.62）の完全平坦性の正則性条件。 -/
theorem powerRootPrismMonicHodgeTate_varpi_regular :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateAlgebra W hW f
    IsSMulRegular T v := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateAlgebra W hW f
  have he : Ideal.span {(φ v) ^ p} = Ideal.span {(p : T)} := by
    simpa only [Ideal.map_span, Set.image_singleton, map_pow, map_natCast] using
      congrArg (Ideal.map φ) (perfectPrismVarpi_span_pow W hW)
  have h := regular_of_span_power_eq (φ v) (p : T) p hp he
    (powerRootPrismMonic_pdCompletion_hodgeTate_prime_regular W hW hpR f hf)
  exact h

include hpR hf hdeg in
/-- 概要：正次数モニック入力の自然な Hodge–Tate 候補は ϖ 完全忠実平坦。
方針：基底・候補の ϖ 正則性と自然な剰余の忠実平坦性を正則主元判定へ渡す。
規約：prism 商の p 正則性を明示する。
使われ方：BS Rem 7.15（著者版 p.62）の p 完全忠実平坦性への入力。 -/
theorem powerRootPrismMonicHodgeTate_varpi_completelyFaithfullyFlat :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateAlgebra W hW f
    IsCompletelyFaithfullyFlat (Ideal.span {v}) T := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateAlgebra W hW f
  let := adicQuotientAlgebra (Ideal.span {v}) T
  have hvR := regular_of_span_power_eq v (p : R) p hp (perfectPrismVarpi_span_pow W hW) hpR
  let := powerRootPrismMonicHodgeTateVarpi_faithfullyFlat W hW f hf hdeg
  have hFF := Module.FaithfullyFlat.of_linearEquiv (R ⧸ Ideal.span {v})
    (T ⧸ Ideal.map (algebraMap R T) (Ideal.span {v}))
    (Algebra.TensorProduct.quotIdealMapEquivQuotTensor T (Ideal.span {v})).symm.toLinearEquiv
  exact isCompletelyFaithfullyFlat_principal_of_regular v hvR T
    (powerRootPrismMonicHodgeTate_varpi_regular W hW hpR f hf) hFF

include hpR hf hdeg in
/-- 概要：正次数モニック入力の自然な Hodge–Tate 候補は p 完全平坦。
方針：ϖ 完全平坦性を p 乗へ移し、(ϖ^p)=(p) で書き換える。
規約：p 剰余の忠実性は別途接続する。
使われ方：BS Rem 7.15（著者版 p.62）の p 完全忠実平坦性の第一条件。 -/
theorem powerRootPrismMonicHodgeTate_prime_completelyFlat :
    let := pdCompletionCommRing L p (jL dP)
    let := powerRootPrismMonicHodgeTateAlgebra W hW f
    IsCompletelyFlat (Ideal.span {(p : R)}) T := by
  let := pdCompletionCommRing L p (jL dP)
  let := powerRootPrismMonicHodgeTateAlgebra W hW f
  have h := isCompletelyFlat_principal_power v T
    (powerRootPrismMonicHodgeTate_varpi_completelyFaithfullyFlat W hW hpR f hf hdeg).1 p
  rwa [perfectPrismVarpi_span_pow W hW] at h

end SerrePositivity.BhattScholze.Andre
