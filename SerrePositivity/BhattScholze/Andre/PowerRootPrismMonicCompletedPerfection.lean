module

public import SerrePositivity.BhattScholze.Andre.RawDivisionPDPerfectionComparison
public import SerrePositivity.BhattScholze.Andre.PowerRootPrismMonicCompletionUniversal

/-!
# André E1・E2：元の無限根モニック実候補の完全 δ 化と perfectoid 商

## 概要

元の raw 包の実完備化を δ 完全化し再完備化した生成元商は整 perfectoid。
元の Hodge–Tate 候補から自然に写り、元の多項式の根を標準射で送る。
BS Cor 7.3（著者版 p.56）、Rem 7.15（p.62）の構成比較。

## 方針

任意 raw 包の一般比較を無限根モニック入力に適用する。
標準分母像を殺す自然射を商へ降ろし、多項式評価の自然性で根を移す。

## 規約

この完全化を経る基底射の p 完全忠実平坦性の保存は別工程。
perfectoid 性と根だけで一般存在目標の完成とは数えない。

## 使われ方

元の実候補の平坦性を最終 perfectoid 候補へ移す際の、同じ対象と標準射の固定。
-/

@[expose] public noncomputable section
universe u
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
/-- 概要：係数射で評価して零となる根は、任意の環射で送っても根。
方針：多項式評価と環射の可換性を使う。
規約：可換環を任意に扱う。
使われ方：BS Rem 7.15（著者版 p.62）の標準比較による根の移送。 -/
theorem polynomialRoot_mapRingHom {R S U : Type u} [CommRing R] [CommRing S] [CommRing U]
    (f : Polynomial R) (φ : R →+* S) (g : S →+* U) (r : S) (hr : f.eval₂ φ r = 0) :
    f.eval₂ (g.comp φ) (g r) = 0 := by
  rw [← Polynomial.hom_eval₂, hr, map_zero]

variable {A : Type u} [CommRing A] {p : ℕ} [Fact p.Prime]
variable (W : OrientedPrism p A) (hW : W.deltaStructure.IsPerfect) (f : Polynomial A)
local notation "hp" => Nat.Prime.pos (Fact.out : p.Prime)
local notation "P" => PowerRootPolynomial A p hp
local notation "E" => powerRootPolynomialDelta p hW.p_mul_injective W.deltaStructure
local notation "dP" => algebraMap A P W.generator
local notation "xP" => algebraMap A P (perfectPrismVarpiLift W hW)
local notation "a" => powerRootPrismMonicUnaryFamily (p := p) f
local notation "L" => DeltaAdjoinDivision E dP a
local notation "jL" => deltaAdjoinDivisionMap E dP a
local notation "H" => PDCompletionH0 L p (jL dP)
local notation "uL" => pdCompletionUnit L p (jL dP)
local notation "dH" => uL (jL dP)
local notation "xH" => uL (jL xP)
local notation "T" => H ⧸ Ideal.span {dH}
local notation "qH" => Ideal.Quotient.mk (Ideal.span {dH})
local notation "R" => A ⧸ W.ideal
local notation "S" => H ⧸ Ideal.span {dH, xH}



local notation "DH" => deltaPDCompletionStructure (deltaAdjoinDivisionStructure E dP a) (jL dP)
local notation "C" => DeltaPerfection DH
local notation "x" => deltaPerfectionOf DH 0 dH
local notation "H∞" => PDCompletionH0 C p x
local notation "sC" => pdCompletionUnit C p x
local notation "T∞" => H∞ ⧸ Ideal.span {sC x}
local notation "q∞" => Ideal.Quotient.mk (Ideal.span {sC x})
local notation "hdP" => powerRootPrismGenerator_isDistinguished W hW

/-- 概要：元の実候補の完全 δ 化後の商は既存の perfectoid 候補と環同型。
方針：任意 raw 包の実完備化先行比較を同じ入力へ適用する。
規約：モニック性・正次数・prism 商の p 正則性は不要。
使われ方：BS Cor 7.3（著者版 p.56）、Rem 7.15（p.62）の最終候補の固定。 -/
def powerRootPrismMonicCompletedPerfectionQuotientEquiv :
    let := pdCompletionCommRing L p (jL dP)
    let := pdCompletionCommRing C p x
    let := divisionPrismCommRing E dP a
    T∞ ≃+* DivisionPerfectoidCandidate E dP a hdP := by
  let := pdCompletionCommRing L p (jL dP)
  let := pdCompletionCommRing C p x
  let := divisionPrismCommRing E dP a
  exact rawDivisionPDPerfectionQuotientEquiv E dP a hdP

/-- 概要：完全 δ 化後の同じ標準生成元商は整 perfectoid。
方針：一般の raw 比較から整 perfectoid 性を受け取る。
規約：平坦性をこの主張に含めない。
使われ方：BS Cor 7.3（著者版 p.56）、Rem 7.15（p.62）の根付き候補の環性質。 -/
theorem powerRootPrismMonicCompletedPerfection_isIntegralPerfectoid :
    let := pdCompletionCommRing L p (jL dP)
    let := pdCompletionCommRing C p x
    IsIntegralPerfectoid T∞ p := by
  let := pdCompletionCommRing L p (jL dP)
  let := pdCompletionCommRing C p x
  exact rawDivisionPDPerfectionQuotient_isIntegralPerfectoid E dP a hdP

set_option maxHeartbeats 2000000 in
-- 元の実 H⁰ とその完全化後の実 H⁰ の二つの巨大な環構造の照合に必要。
/-- 概要：元の Hodge–Tate 候補から完全 δ 化後の perfectoid 商への自然射。
方針：実 H⁰ の完全化標準射が元の分母像を殺すことから商へ降ろす。
規約：元の raw 包・実 H⁰ と標準射を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の根と基底作用の追跡。 -/
def powerRootPrismMonicHodgeTateToCompletedPerfection :
    let := pdCompletionCommRing L p (jL dP)
    let := pdCompletionCommRing C p x
    T →+* T∞ := by
  let := pdCompletionCommRing L p (jL dP)
  let G := DH
  let Cp := DeltaPerfection G
  let i := deltaPerfectionOf G 0
  let xp := i dH
  let := pdCompletionCommRing Cp p xp
  let unitC := pdCompletionUnit Cp p xp
  let qC := Ideal.Quotient.mk (Ideal.span {unitC xp})
  let k := qC.comp (unitC.comp i)
  apply Ideal.Quotient.lift (Ideal.span {dH}) k
  change Ideal.span {dH} ≤ RingHom.ker k
  apply Ideal.span_le.mpr
  intro z hz
  rcases Set.mem_singleton_iff.mp hz with rfl
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self (unitC xp))

/-- 概要：完全 δ 化後の商への基底射は元の自然基底射の合成。
方針：二つの標準射を合成する。
規約：基底は元の prism 商 R。
使われ方：BS Rem 7.15（著者版 p.62）の平坦性を定式化する係数射。 -/
def powerRootPrismMonicCompletedPerfectionBaseMap :
    let := pdCompletionCommRing L p (jL dP)
    let := pdCompletionCommRing C p x
    R →+* T∞ := by
  let := pdCompletionCommRing L p (jL dP)
  let := pdCompletionCommRing C p x
  exact (powerRootPrismMonicHodgeTateToCompletedPerfection W hW f).comp
    (powerRootPrismMonicHodgeTateBaseMap W hW f)

/-- 概要：完全 δ 化後の根は元の実候補の指定根の標準像。
方針：検証済みの根を自然比較射で送る。
規約：別の根を選択し直さない。
使われ方：BS Rem 7.15（著者版 p.62）の同じ候補の根方程式。 -/
def powerRootPrismMonicCompletedPerfectionRoot :
    let := pdCompletionCommRing L p (jL dP)
    let := pdCompletionCommRing C p x
    T∞ := by
  let := pdCompletionCommRing L p (jL dP)
  let := pdCompletionCommRing C p x
  exact powerRootPrismMonicHodgeTateToCompletedPerfection W hW f
    (powerRootPrismMonicHodgeTateRoot W hW f)

/-- 概要：完全 δ 化後の指定根も元の多項式の係数商の根。
方針：評価と環射の可換性で元の実候補の根方程式を送る。
規約：モニック性・正次数・prism 商の p 正則性は不要。
使われ方：BS Rem 7.15（著者版 p.62）の根付き perfectoid 候補。 -/
theorem powerRootPrismMonicCompletedPerfectionRoot_eval :
    let := pdCompletionCommRing L p (jL dP)
    let := pdCompletionCommRing C p x
    (f.map (Ideal.Quotient.mk W.ideal)).eval₂
      (powerRootPrismMonicCompletedPerfectionBaseMap W hW f)
      (powerRootPrismMonicCompletedPerfectionRoot W hW f) = 0 := by
  let := pdCompletionCommRing L p (jL dP)
  let := pdCompletionCommRing C p x
  exact polynomialRoot_mapRingHom (f.map (Ideal.Quotient.mk W.ideal))
    (powerRootPrismMonicHodgeTateBaseMap W hW f)
    (powerRootPrismMonicHodgeTateToCompletedPerfection W hW f)
    (powerRootPrismMonicHodgeTateRoot W hW f) (powerRootPrismMonicHodgeTateRoot_eval W hW f)

/-- 概要：完全化後の商比較は全ての無限根入力係数の標準像を保つ。
方針：一般 raw 比較の係数射公式を入力環の元で評価する。
規約：全ての入力環元 r を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の既存候補との基底作用の一致。 -/
theorem powerRootPrismMonicCompletedPerfectionQuotientEquiv_coeff (r : P) :
    let := pdCompletionCommRing L p (jL dP)
    let := pdCompletionCommRing C p x
    let := divisionPrismCommRing E dP a
    powerRootPrismMonicCompletedPerfectionQuotientEquiv W hW f
      (q∞ (sC (deltaPerfectionOf DH 0 (uL (jL r))))) =
      divisionPerfectoidCandidateMap E dP a hdP r := by
  let := pdCompletionCommRing L p (jL dP)
  let := pdCompletionCommRing C p x
  let := divisionPrismCommRing E dP a
  exact RingHom.congr_fun (rawDivisionPDPerfectionQuotientEquiv_comp_coefficient E dP a hdP) r

end SerrePositivity.BhattScholze.Andre
