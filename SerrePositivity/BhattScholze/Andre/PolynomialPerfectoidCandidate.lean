module

public import SerrePositivity.BhattScholze.Andre.DivisionPerfectoidCandidate
public import SerrePositivity.BhattScholze.Andre.MonicRelation
public import SerrePositivity.BhattScholze.PolynomialRankOneDelta

/-!
# André E1：多項式族の根方程式を保つ perfectoid 候補

## 概要

完全 prism の商の多項式族について、係数を持ち上げて独立変数の関係式を δ 除算する。
構成した候補は perfectoid で、指定多項式の根を持つ。
BS 著者版 Thm 7.14（p.61）、Rem 7.15（p.62）の一段構成の根方程式を扱う。

## 方針

係数 lift は通常の多項式写像の全射性から選び、rank-one 多項式 δ 環の変数で評価する。
任意関係族の δ 除算・完全化・prism 商で関係が消えることを利用する。
原典の Prop 7.11 を使う証明とは異なる構成である。

## 規約

ここではモニック性も正次数も使わない。候補が零環になることを排除しておらず、
p 完全忠実平坦性を含む目標定理とは区別する。

## 使われ方

pd 包の計算から基底射の p 完全忠実平坦性を供給する際、同じ候補の根方程式を再利用する。
-/

@[expose] public noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)

local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => fun s : σ => monicRelation (f s) s
local notation "c" => (MvPolynomial.C : A →+* MvPolynomial σ A)

/-- 概要：多項式関係族を課す候補 prism の台環構造。
方針：任意関係族の構成を多項式 δ 環に適用する。
規約：平坦性を要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の具体的候補。 -/
@[instance_reducible] def polynomialPrismCommRing :
    CommRing (DivisionPrismCarrier E (c d) r) :=
  divisionPrismCommRing E (c d) r

/-- 概要：多項式族に対する具体的な perfectoid 商候補。
方針：rank-one 変数の多項式関係を δ 除算する。
規約：モニック性・正次数のない一般族を許し、零候補も許す。
使われ方：BS Thm 7.14（著者版 p.61）の根方程式を保持する。 -/
abbrev PolynomialPerfectoidCandidate (hd : D.IsDistinguished d) :=
  letI := polynomialPrismCommRing D d f
  DivisionPerfectoidCandidate E (c d) r
    ((polynomialRankOneDeltaStructure_C_isDeltaHom σ D).map_isDistinguished hd)

/-- 概要：元の係数環から多項式族の候補への射。
方針：多項式係数包含と任意関係族の候補射を合成する。
規約：この射の忠実平坦性は別の証明義務。
使われ方：BS Rem 7.15（著者版 p.62）の係数作用を固定する。 -/
def polynomialPerfectoidCandidateCoefficientMap (hd : D.IsDistinguished d) :
    letI := polynomialPrismCommRing D d f
    A →+* PolynomialPerfectoidCandidate D d f hd := by
  let := polynomialPrismCommRing D d f
  exact (divisionPerfectoidCandidateMap E (c d) r
    ((polynomialRankOneDeltaStructure_C_isDeltaHom σ D).map_isDistinguished hd)).comp c

/-- 概要：各多項式の根を表す候補の元。
方針：独立変数の候補への像を取る。
規約：根の条件は次の定理で証明する。
使われ方：BS Thm 7.14（著者版 p.61）の一段の根族。 -/
def polynomialPerfectoidCandidateRoot (hd : D.IsDistinguished d) (s : σ) :
    letI := polynomialPrismCommRing D d f
    PolynomialPerfectoidCandidate D d f hd := by
  let := polynomialPrismCommRing D d f
  exact divisionPerfectoidCandidateMap E (c d) r
    ((polynomialRankOneDeltaStructure_C_isDeltaHom σ D).map_isDistinguished hd) (MvPolynomial.X s)

/-- 概要：多項式族の具体的候補は整 perfectoid。
方針：任意関係族の候補の perfectoid 性を適用する。
規約：零環も含み、忠実平坦性は含まない。
使われ方：BS Thm 7.14（著者版 p.61）の別経路の一段候補。 -/
theorem polynomialPerfectoidCandidate_isIntegralPerfectoid (hd : D.IsDistinguished d) :
    letI := polynomialPrismCommRing D d f
    IsIntegralPerfectoid (PolynomialPerfectoidCandidate D d f hd) p := by
  let := polynomialPrismCommRing D d f
  exact divisionPerfectoidCandidate_isIntegralPerfectoid E (c d) r
    ((polynomialRankOneDeltaStructure_C_isDeltaHom σ D).map_isDistinguished hd)

/-- 概要：候補の指定元は元の係数射に関して f の根となる。
方針：環射による多項式評価の自然性と、除算した関係元の消滅を使う。
規約：任意多項式族に成立するが候補が非零とは限らない。
使われ方：BS Rem 7.15（著者版 p.62）の根方程式を完全化後まで保持する。 -/
theorem polynomialPerfectoidCandidate_eval (hd : D.IsDistinguished d) (s : σ) :
    letI := polynomialPrismCommRing D d f
    (f s).eval₂ (polynomialPerfectoidCandidateCoefficientMap D d f hd)
      (polynomialPerfectoidCandidateRoot D d f hd s) = 0 := by
  let := polynomialPrismCommRing D d f
  let hdC := (polynomialRankOneDeltaStructure_C_isDeltaHom σ D).map_isDistinguished hd
  exact (Polynomial.hom_eval₂ (f s) c (divisionPerfectoidCandidateMap E (c d) r hdC)
    (MvPolynomial.X s)).symm.trans
      (divisionPerfectoidCandidateMap_relation E (c d) r hdC s)

/-- 概要：候補係数射は基底の d を消す。
方針：多項式係数としての d の消滅を使う。
規約：商からの基底射を定めるための結果である。
使われ方：BS Thm 7.14（著者版 p.61）の基底商を保つ。 -/
theorem polynomialPerfectoidCandidateCoefficientMap_d (hd : D.IsDistinguished d) :
    letI := polynomialPrismCommRing D d f
    polynomialPerfectoidCandidateCoefficientMap D d f hd d = 0 := by
  let := polynomialPrismCommRing D d f
  exact divisionPerfectoidCandidateMap_d E (c d) r
    ((polynomialRankOneDeltaStructure_C_isDeltaHom σ D).map_isDistinguished hd)

/-- 概要：元の d 商から多項式根を持つ候補への基底射。
方針：係数射を d 商に降ろす。
規約：平坦性は結論しない。
使われ方：BS Thm 7.14（著者版 p.61）の元の perfectoid 基底の作用。 -/
def polynomialPerfectoidCandidateBaseMap (hd : D.IsDistinguished d) :
    letI := polynomialPrismCommRing D d f
    A ⧸ Ideal.span {d} →+* PolynomialPerfectoidCandidate D d f hd := by
  let := polynomialPrismCommRing D d f
  apply Ideal.Quotient.lift _ (polynomialPerfectoidCandidateCoefficientMap D d f hd)
  change Ideal.span {d} ≤ RingHom.ker (polynomialPerfectoidCandidateCoefficientMap D d f hd)
  apply Ideal.span_le.mpr
  intro x hx
  have hxd : x = d := Set.mem_singleton_iff.mp hx
  subst x
  exact polynomialPerfectoidCandidateCoefficientMap_d D d f hd

end SerrePositivity.BhattScholze.Andre
