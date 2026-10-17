module

public import SerrePositivity.BhattScholze.Andre.Unconditional.InitialCoefficient.Comparison
public import SerrePositivity.BhattScholze.Andre.Unconditional.PowerRootAResidue
public import SerrePositivity.BhattScholze.DeltaAdjoinDivisionResidueFlat

/-!
# A1-d：元の係数商上の raw 残余商と実還元 H⁰ の忠実平坦性

## 概要
初期係数商の通常モニック比較を一般の raw 残余商の忠実平坦性へ合成する。
BS Rem 7.15（著者版 p.62）の A1-b の鎖の第一段を供給する。

## 方針
元の全係数で合成射を照合し、A1-b の自然な係数制限作用と既存 H⁰ 比較へ移す。

## 規約
元の raw 包・実自由 δ 源・係数射を保ち、hpR は仮定しない。

## 使われ方
実逐次完備化の純性と生成元の正則性へ渡す入力。完備化後の主張はここでは証明しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.BhattScholze.Andre.InitialCoefficient
open CategoryTheory
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L₀" => PowerRootUnaryFreeDeltaRing A p hp
local notation "Qinit" => P ⧸ deltaDivisionFirstBaseIdeal (p := p) dP a
local notation "R" => A ⧸ Ideal.span {(p : A), W.generator}
local notation "Q₀" => L₀ ⧸ Ideal.span {(p : L₀), MvPolynomial.C dP}
local notation "κ" => powerRootSourceQuotientCoefficientMap_of_unconditional W
local notation "ψ" => powerRootPrismMonicSourceQuotientResidueMap_of_unconditional W hW f
local notation "Res" => DeltaAdjoinDivisionResidue E dP a
local notation "hd" => powerRootPrismGenerator_isDistinguished W hW
local notation "hpP" => powerRootPolynomial_primeRegular p hW.p_mul_injective

include hW in
/-- 概要：元の無限根自由 δ 源でも p の乗算は単射。
方針：完全 prism の p 正則性を自由多項式環へ平坦移送する。
規約：prism 商の p 正則性とは異なり、hpR を要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の一般 raw 残余商の既存 API への入力。 -/
theorem freeDelta_prime_regular : Function.Injective (fun x : L₀ => (p : L₀) * x) := by
  simpa only [map_natCast, IsSMulRegular, smul_eq_mul] using
    (show IsSMulRegular P (p : P) from hpP).of_flat (S := L₀)

local notation "hpL" => freeDelta_prime_regular W hW
local notation "hg" => witt_ghostMap_injective_of_mul_prime_injective p L₀ hpL
local notation "j" => deltaAdjoinDivisionMap E dP a
local notation "r" => Ideal.Quotient.mk (deltaAdjoinDivisionResidueIdeal E dP a)

/-- 概要：初期商を経由した A/(p,d) から raw 残余商への係数射。
方針：検証済みの二つの標準係数射を合成する。
規約：必要な p 正則性・ghost 単射性・distinguished 単元は内部供給する。
使われ方：BS Rem 7.15（著者版 p.62）の元の係数作用での忠実平坦性。 -/
def rawResidueBaseMap : R →+* Res :=
  (deltaAdjoinDivisionResidueBaseMap E hpP hpL hg dP a (hd).unit (hd).unit_spec).comp
    (initialCoefficientBaseMap (p := p) W.generator f)

/-- 概要：合成係数射は元の A の全係数の標準 raw 剰余像に一致する。
方針：初期商と raw 残余商への代表元公式を順に使う。
規約：任意の係数を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の自然な作用の確認。 -/
theorem rawResidueBaseMap_mk (x : A) :
    rawResidueBaseMap W hW f (Ideal.Quotient.mk _ x) = r (j (algebraMap A P x)) := by
  rw [rawResidueBaseMap, RingHom.comp_apply, initialCoefficientBaseMap_mk,
    deltaAdjoinDivisionResidueBaseMap_mk]

/-- 概要：初期商を経由した係数射は A1-b の実源商を経由する係数射と同じ。
方針：A/(p,d) の全代表元で二つの合成を比較する。
規約：初期商 Qinit と自由 δ 源商 Q₀ を同一視しない。
使われ方：BS Rem 7.15（著者版 p.62）の受渡し指定の自然な R 作用を保証する。 -/
theorem rawResidueBaseMap_eq_source : rawResidueBaseMap W hW f = (ψ).comp κ := by
  apply Ideal.Quotient.ringHom_ext
  apply RingHom.ext
  intro x
  rw [RingHom.comp_apply, rawResidueBaseMap_mk]
  change r (j (algebraMap A P x)) = r (j
    (deltaDivisionSourceEval E a (MvPolynomial.C (algebraMap A P x))))
  rw [deltaDivisionSourceEval_C]

/-- 概要：検証済みの自然な係数射による raw 残余商の R 代数構造。
方針：元の合成環射から定める。
規約：既存の自然係数制限作用との一致は上の射の等式で保証する。
使われ方：BS Rem 7.15（著者版 p.62）の忠実平坦性の合成。 -/
@[instance_reducible] def rawResidueAlgebra : Algebra R Res :=
  (rawResidueBaseMap W hW f).toAlgebra

/-- 概要：元の raw 残余商は合成係数射によって A/(p,d) 上忠実平坦。
方針：初期商の忠実平坦性と既存の初期商上の raw 残余商の忠実平坦性を合成する。
規約：モニック性・正次数以外の追加仮定を置かない。
使われ方：BS Rem 7.15（著者版 p.62）の A1-b 指定作用への移送の入力。 -/
theorem rawResidueBase_faithfullyFlat (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    let := rawResidueAlgebra W hW f
    Module.FaithfullyFlat R Res := by
  let := initialCoefficientAlgebra (p := p) W.generator f
  let := deltaAdjoinDivisionResidueBaseAlgebra E hpP hpL hg dP a (hd).unit (hd).unit_spec
  let := rawResidueAlgebra W hW f
  let : IsScalarTower R Qinit Res := IsScalarTower.of_algebraMap_eq' rfl
  let := initialCoefficient_faithfullyFlat (p := p) W.generator f hf hdeg
  let := deltaAdjoinDivisionResidue_moduleFaithfullyFlat E hpP hpL hg dP a (hd).unit (hd).unit_spec
  exact Module.FaithfullyFlat.trans R Qinit Res

local notation "MRes" => (CategoryTheory.Functor.obj
  (ModuleCat.restrictScalars κ) (ModuleCat.of Q₀ Res) : ModuleCat R)

/-- 概要：A1-b の指定係数制限作用と初期商経由の作用は同じ元を保つ線形同型で結ばれる。
方針：全係数での合成射の一致をスカラー作用の一致へ移す。
規約：元の Res の元を変更しない。
使われ方：BS Rem 7.15（著者版 p.62）の正確な受渡し型への忠実平坦性の移送。 -/
def rawResidueRestrictionLinearEquiv :
    letI := (ψ).toAlgebra
    letI : Module Q₀ Res := Algebra.toModule
    letI := rawResidueAlgebra W hW f
    MRes ≃ₗ[R] Res := by
  letI := (ψ).toAlgebra
  letI : Module Q₀ Res := Algebra.toModule
  letI := rawResidueAlgebra W hW f
  refine
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := ?_ }
  intro c x
  change Res at x
  change ψ (κ c) * x = rawResidueBaseMap W hW f c * x
  rw [rawResidueBaseMap_eq_source]
  rfl

/-- 概要：A1-b の指定した κ による係数制限のまま、raw 残余商は忠実平坦。
方針：初期商を経由した忠実平坦性を同じ元を保つ線形同型で移す。
規約：受渡しの正確な型を保ち、hpR を置かない。
使われ方：BS Rem 7.15（著者版 p.62）の元の A 係数の実還元 H⁰ への入力。 -/
theorem rawResidue_faithfullyFlat (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    letI := (ψ).toAlgebra
    letI : Module Q₀ Res := Algebra.toModule
    Module.FaithfullyFlat R MRes := by
  let := (ψ).toAlgebra
  let : Module Q₀ Res := Algebra.toModule
  let := rawResidueAlgebra W hW f
  let := rawResidueBase_faithfullyFlat W hW f hf hdeg
  exact Module.FaithfullyFlat.of_linearEquiv R Res
    (rawResidueRestrictionLinearEquiv W hW f)

/-- 概要：元の A/(p,d) による実導来還元の H⁰ は忠実平坦。
方針：既存の A1-b の実 H⁰ 比較へ指定作用での raw 残余商の忠実平坦性を渡す。
規約：モニック性・正次数だけを追加し、hpR・Tor 消滅・平坦性は追加しない。
使われ方：BS Rem 7.15（著者版 p.62）の A1-b の次の純性・正則性接続への受渡し。 -/
theorem sourceResidueH0_faithfullyFlat (hf : f.Monic) (hdeg : 0 < f.natDegree) :
    Module.FaithfullyFlat R
      ((DerivedCategory.homologyFunctor (ModuleCat R) 0).obj
        ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk
          (Ideal.span {(p : A), W.generator}))).obj
          (PowerRootPrismMonicSourceCoefficientObject_of_unconditional W hW f)).obj) := by
  let := (ψ).toAlgebra
  let : Module Q₀ Res := Algebra.toModule
  let := rawResidue_faithfullyFlat W hW f hf hdeg
  exact Module.FaithfullyFlat.of_linearEquiv R MRes
    (powerRootPrismMonicSourceCoefficientPDResidueH0Iso_of_unconditional W hW f hf).toLinearEquiv

end SerrePositivity.BhattScholze.Andre.InitialCoefficient
