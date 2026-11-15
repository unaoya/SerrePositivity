module

public import SerrePositivity.BhattScholze.Semiperfectoid.Perfection.PerfectPrismDivision
public import SerrePositivity.BhattScholze.Prism.Perfection.PrismPerfection
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismPerfectoid
public import SerrePositivity.BhattScholze.Andre.OrdinaryRoots.Adjoin
public import SerrePositivity.BhattScholze.Delta.Free.RelativeFreeDelta
public import SerrePositivity.BhattScholze.Andre.Perfection.DeltaAlgebra
public import SerrePositivity.CommutativeAlgebra.KoszulRegular.MonicRelation
public import SerrePositivity.BhattScholze.Andre.Envelope.RootResidueKoszul
public import Mathlib.RingTheory.Regular.Flat
public import SerrePositivity.BhattScholze.Andre.Envelope.FamilyEvaluation
public import SerrePositivity.BhattScholze.Andre.Envelope.RootFamilySource
public import SerrePositivity.BhattScholze.Andre.Envelope.DivisionResidue
public import SerrePositivity.BhattScholze.Delta.Division.Source
public import SerrePositivity.HomologicalAlgebra.DerivedPureHomology
public import SerrePositivity.BhattScholze.Prism.Basic.OrientedPrism

/-!
# モニック族の f/d 包と perfectoid 候補（BS 著者版 Proposition 7.11 を R̃ に当てる部分）

## 概要
任意関係族の δ 除算と多項式族の根方程式を保つ perfectoid 候補、モニック族の最初の・全有限 δ 深さの剰余 Koszul 分解、残余導来評価比較、係数側の導来剰余比較、自由 δ 源商上の導来還元、PD 先行 δ 完全化と多項式 prism 候補の比較、候補の基底射。

## 方針
原典は R̃ に BS 著者版 Proposition 7.11(2) を当てる。Lean は f/d 包を直接作り、Koszul 計算で平坦性を出す。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`Envelope/MonicSource`、`Perfection/PerfectPrismMonic`、`PowerRootEnvelope/Unconditional/Residue`、`Variants/ArbitraryFamily`、`Variants/Auxiliary`、`Variants/MonicRootedExtension`、`Variants/RootedExtension`。
-/

universe u

/-! ## André：任意関係族の δ 除算による perfectoid 候補

## 概要

distinguished 元 d を持つ δ 環で、任意の元族 a を d で除算し、完全化した完全 prism の
商を構成する。商では d と各 a の像が零になる。
BS 著者版 Proposition 3.13（pp.33–35）、BS 著者版 Theorem 7.14（p.61）、BS 著者版 Remark 7.15（p.62）に対応する候補である。

## 方針

冪根関係の比較 の候補構成のうち、冪根関係の形に依存しない部分を一般の元族で再構成する。
既存の p 進完備 δ 完全化と実導来 (p,d) 完備化を使う。
原典の BS 著者版 Proposition 7.11 を使う証明とは異なる経路の構成部分である。

## 規約

元族の正則性や商の非零性を仮定せず、候補が零環になる場合も許す。
基底射の平坦性・忠実性はこのファイルでは証明しない。

## 使われ方

任意モニック多項式を独立変数で評価した元族を入力し、根方程式と perfectoid 性を保持する。
-/

@[expose] public noncomputable section DivisionPerfectoidCandidate

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

open _root_.SerrePositivity.DerivedCompletion

variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A)

local notation "C" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PCompletedDeltaDivision D d a
local notation "j" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap D d a
local notation "E" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure D d a

/-- 概要：任意関係族を除算した完全 δ 環の実 (p,d) 完備化の台集合。
方針：既存の実完備化 H⁰ を使う。
規約：環構造は `divisionPrismCommRing` で明示する。
使われ方：BS 著者版 Proposition 3.13（著者版 pp.33–35）の候補構成部分。 -/
abbrev DivisionPrismCarrier := PDCompletionH0 C p (j d)

/-- 概要：実 H⁰ の既存可換環構造を候補に入れる。
方針：`pdCompletionCommRing` を使用する。
規約：明示的に局所導入する。
使われ方：BS 著者版 Proposition 3.13（著者版 pp.33–35）の候補。 -/
@[instance_reducible] def divisionPrismCommRing : CommRing (DivisionPrismCarrier D d a) :=
  pdCompletionCommRing C p (j d)

/-- 概要：任意の関係族から完全 prism 候補を構成する。
方針：distinguished 性を δ 射で移し、完全 δ 環の実完備化定理を適用する。
規約：忠実平坦性を結論しない。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の別経路の一段候補。 -/
def divisionPrism (hd : D.IsDistinguished d) :
    letI := divisionPrismCommRing D d a
    OrientedPrism p (DivisionPrismCarrier D d a) := by
  let := divisionPrismCommRing D d a
  exact perfectDeltaPDPrism E (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivision_isPerfect D d a) (j d)
    ((_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap_isDeltaHom D d a).map_isDistinguished hd)

/-- 概要：構成した候補 prism の δ 構造は完全。
方針：完全 δ 環の実完備化についての既存定理を適用する。
規約：任意元族を扱う。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の perfectoid 商を得る。 -/
theorem divisionPrism_isPerfect (hd : D.IsDistinguished d) :
    letI := divisionPrismCommRing D d a
    (divisionPrism D d a hd).deltaStructure.IsPerfect := by
  let := divisionPrismCommRing D d a
  exact perfectDeltaPDPrism_isPerfect E (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivision_isPerfect D d a) (j d)
    ((_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap_isDeltaHom D d a).map_isDistinguished hd)

/-- 概要：完全 prism 候補の標準商を perfectoid 候補とする。
方針：prism の定義イデアルで割る。
規約：零環を許す。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の根付き拡大の台環の候補。 -/
abbrev DivisionPerfectoidCandidate (hd : D.IsDistinguished d) :=
  letI := divisionPrismCommRing D d a
  DivisionPrismCarrier D d a ⧸ (divisionPrism D d a hd).ideal

/-- 概要：構成した商候補は整 perfectoid。
方針：完全 prism の商と perfectoid 環の対応を使う。
規約：平坦性は未証明である。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の別経路の構成部分。 -/
theorem divisionPerfectoidCandidate_isIntegralPerfectoid (hd : D.IsDistinguished d) :
    letI := divisionPrismCommRing D d a
    IsIntegralPerfectoid (DivisionPerfectoidCandidate D d a hd) p := by
  let := divisionPrismCommRing D d a
  exact (divisionPrism D d a hd).quotient_isIntegralPerfectoid
    (divisionPrism_isPerfect D d a hd)

/-- 概要：元の δ 環から perfectoid 候補への具体的な係数射。
方針：δ 除算完全化、実完備化、prism 商の射を合成する。
規約：忠実性を仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の関係式を商へ移す。 -/
def divisionPerfectoidCandidateMap (hd : D.IsDistinguished d) :
    letI := divisionPrismCommRing D d a
    A →+* DivisionPerfectoidCandidate D d a hd := by
  let := divisionPrismCommRing D d a
  exact (Ideal.Quotient.mk (divisionPrism D d a hd).ideal).comp
    ((pdCompletionUnit C p (j d)).comp j)

/-- 概要：候補への係数射は d を零へ送る。
方針：d の完備化像が prism の選択生成元であることを使う。
規約：任意関係族を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の基底商からの射を作る。 -/
theorem divisionPerfectoidCandidateMap_d (hd : D.IsDistinguished d) :
    letI := divisionPrismCommRing D d a
    divisionPerfectoidCandidateMap D d a hd d = 0 := by
  let := divisionPrismCommRing D d a
  change Ideal.Quotient.mk (divisionPrism D d a hd).ideal
    (divisionPrism D d a hd).generator = 0
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- 概要：各指定関係元の候補における像は零。
方針：δ 除算完全化では d で割り切れ、最後の商では d が零となる。
規約：モニック性・正則性は不要である。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の多項式の根方程式を保持する。 -/
theorem divisionPerfectoidCandidateMap_relation (hd : D.IsDistinguished d) (s : σ) :
    letI := divisionPrismCommRing D d a
    divisionPerfectoidCandidateMap D d a hd (a s) = 0 := by
  let := divisionPrismCommRing D d a
  let q := (Ideal.Quotient.mk (divisionPrism D d a hd).ideal).comp
    (pdCompletionUnit C p (j d))
  obtain ⟨z, hz⟩ := _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap_dvd D d a s
  change q (j (a s)) = 0
  rw [hz, map_mul]
  have hqd : q (j d) = 0 := divisionPerfectoidCandidateMap_d D d a hd
  rw [hqd, zero_mul]

/-- 概要：元の d 商から perfectoid 候補への基底射。
方針：d が零に写ることを用いて商に降下する。
規約：基底射の忠実平坦性は主張しない。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の候補を元の perfectoid 環の上に置く。 -/
def divisionPerfectoidCandidateBaseMap (hd : D.IsDistinguished d) :
    letI := divisionPrismCommRing D d a
    A ⧸ Ideal.span {d} →+* DivisionPerfectoidCandidate D d a hd := by
  let := divisionPrismCommRing D d a
  apply Ideal.Quotient.lift _ (divisionPerfectoidCandidateMap D d a hd)
  change Ideal.span {d} ≤ RingHom.ker (divisionPerfectoidCandidateMap D d a hd)
  apply Ideal.span_le.mpr
  intro x hx
  have hxd : x = d := Set.mem_singleton_iff.mp hx
  subst x
  exact divisionPerfectoidCandidateMap_d D d a hd

end SerrePositivity.BhattScholze.Andre

end DivisionPerfectoidCandidate

/-! ## André：多項式族の根方程式を保つ perfectoid 候補

## 概要

完全 prism の商の多項式族について、係数を持ち上げて独立変数の関係式を δ 除算する。
構成した候補は perfectoid で、指定多項式の根を持つ。
BS 著者版 Theorem 7.14（p.61）、BS 著者版 Remark 7.15（p.62）の一段構成の根方程式を扱う。

## 方針

係数 lift は通常の多項式写像の全射性から選び、rank-one 多項式 δ 環の変数で評価する。
任意関係族の δ 除算・完全化・prism 商で関係が消えることを利用する。
原典の BS 著者版 Proposition 7.11 を使う証明とは異なる構成である。

## 規約

ここではモニック性も正次数も使わない。候補が零環になることを排除しておらず、
p 完全忠実平坦性を含む目標定理とは区別する。

## 使われ方

pd 包の計算から基底射の p 完全忠実平坦性を供給する際、同じ候補の根方程式を再利用する。
-/

@[expose] public noncomputable section PolynomialPerfectoidCandidate

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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の具体的候補。 -/
@[instance_reducible] def polynomialPrismCommRing :
    CommRing (DivisionPrismCarrier E (c d) r) :=
  divisionPrismCommRing E (c d) r

/-- 概要：多項式族に対する具体的な perfectoid 商候補。
方針：rank-one 変数の多項式関係を δ 除算する。
規約：モニック性・正次数のない一般族を許し、零候補も許す。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の根方程式を保持する。 -/
abbrev PolynomialPerfectoidCandidate (hd : D.IsDistinguished d) :=
  letI := polynomialPrismCommRing D d f
  DivisionPerfectoidCandidate E (c d) r
    ((polynomialRankOneDeltaStructure_C_isDeltaHom σ D).map_isDistinguished hd)

/-- 概要：元の係数環から多項式族の候補への射。
方針：多項式係数包含と任意関係族の候補射を合成する。
規約：この射の忠実平坦性は別の証明義務。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数作用を固定する。 -/
def polynomialPerfectoidCandidateCoefficientMap (hd : D.IsDistinguished d) :
    letI := polynomialPrismCommRing D d f
    A →+* PolynomialPerfectoidCandidate D d f hd := by
  let := polynomialPrismCommRing D d f
  exact (divisionPerfectoidCandidateMap E (c d) r
    ((polynomialRankOneDeltaStructure_C_isDeltaHom σ D).map_isDistinguished hd)).comp c

/-- 概要：各多項式の根を表す候補の元。
方針：独立変数の候補への像を取る。
規約：根の条件は次の定理で証明する。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の一段の根族。 -/
def polynomialPerfectoidCandidateRoot (hd : D.IsDistinguished d) (s : σ) :
    letI := polynomialPrismCommRing D d f
    PolynomialPerfectoidCandidate D d f hd := by
  let := polynomialPrismCommRing D d f
  exact divisionPerfectoidCandidateMap E (c d) r
    ((polynomialRankOneDeltaStructure_C_isDeltaHom σ D).map_isDistinguished hd) (MvPolynomial.X s)

/-- 概要：多項式族の具体的候補は整 perfectoid。
方針：任意関係族の候補の perfectoid 性を適用する。
規約：零環も含み、忠実平坦性は含まない。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の別経路の一段候補。 -/
theorem polynomialPerfectoidCandidate_isIntegralPerfectoid (hd : D.IsDistinguished d) :
    letI := polynomialPrismCommRing D d f
    IsIntegralPerfectoid (PolynomialPerfectoidCandidate D d f hd) p := by
  let := polynomialPrismCommRing D d f
  exact divisionPerfectoidCandidate_isIntegralPerfectoid E (c d) r
    ((polynomialRankOneDeltaStructure_C_isDeltaHom σ D).map_isDistinguished hd)

/-- 概要：候補の指定元は元の係数射に関して f の根となる。
方針：環射による多項式評価の自然性と、除算した関係元の消滅を使う。
規約：任意多項式族に成立するが候補が非零とは限らない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の根方程式を完全化後まで保持する。 -/
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
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の基底商を保つ。 -/
theorem polynomialPerfectoidCandidateCoefficientMap_d (hd : D.IsDistinguished d) :
    letI := polynomialPrismCommRing D d f
    polynomialPerfectoidCandidateCoefficientMap D d f hd d = 0 := by
  let := polynomialPrismCommRing D d f
  exact divisionPerfectoidCandidateMap_d E (c d) r
    ((polynomialRankOneDeltaStructure_C_isDeltaHom σ D).map_isDistinguished hd)

/-- 概要：元の d 商から多項式根を持つ候補への基底射。
方針：係数射を d 商に降ろす。
規約：平坦性は結論しない。
使われ方：BS 著者版 Theorem 7.14（著者版 p.61）の元の perfectoid 基底の作用。 -/
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

end PolynomialPerfectoidCandidate

/-! ## PD 先行 δ 完全化と多項式 prism 候補の標準比較

## 概要

raw f/d 包の PD 完備化・δ 完全化・PD 完備化による環は、既存の多項式 prism 候補と
元の A 係数射を保って同型。BS 著者版 Remark 7.15（著者版 p.62）の二つの候補の比較。

## 方針

既存の一般 PD 完備化挿入比較と p 進完備化挿入比較を合成する。
原典の BS 著者版 Proposition 7.11 を用いる証明とは異なる具体的な標準係数射の計算。

## 規約

任意多項式族で比較し、モニック性・正次数・有限性は使わない。

## 使われ方

PD 先行構成で証明した完全忠実平坦性を、根方程式を持つ既存の prism 候補へ移す。
-/

@[expose] public noncomputable section MonicPrismaticCandidateComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory
open _root_.SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun t : σ => monicRelation (f t) t)
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "F" => deltaAdjoinDivisionStructure E (MvPolynomial.C d) r
local notation "ι" => deltaAdjoinDivisionMap E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "z" => c d
local notation "B" => PDCompletionH0 Raw p z
local notation "G" => deltaPDCompletionStructure F z
local notation "v" => pdCompletionUnit Raw p z
local notation "C" => DeltaPerfection G
local notation "x" => deltaPerfectionOf G 0 (v z)
local notation "H" => PDCompletionH0 C p x
local notation "r₀" => RingHom.comp (RingHom.comp (pdCompletionUnit C p x)
  (deltaPerfectionOf G 0)) v
local notation "W" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PCompletedDeltaDivision E (MvPolynomial.C d) r
local notation "j" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap E (MvPolynomial.C d) r
local notation "T" => DivisionPrismCarrier E (MvPolynomial.C d) r

/-- 概要：raw f/d 包から既存の多項式 prism 台環候補への標準環射。
方針：既存の p 進完備 δ 完全化射と実 PD 完備化単位を合成する。
規約：平坦性を仮定しない具体的な射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の二つの標準 raw 係数射の比較。 -/
def polynomialPrismRawMap :
    letI := polynomialPrismCommRing D d f
    Raw →+* T := by
  let := polynomialPrismCommRing D d f
  exact (pdCompletionUnit W p (j (MvPolynomial.C d))).comp (pCompletedDeltaPerfectionMap F)

/-- 概要：元の A から既存の多項式 prism 台環候補への標準係数射。
方針：raw 候補射と raw 包の元の A 係数射を合成する。
規約：perfectoid 商を取る前の係数射である。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の候補の完全忠実平坦性を述べる。 -/
def polynomialPrismCoefficientMap :
    letI := polynomialPrismCommRing D d f
    A →+* T := by
  let := polynomialPrismCommRing D d f
  exact (polynomialPrismRawMap D d f).comp c

/-- 概要：PD 先行完全化の実環は、既存の多項式 prism 台環候補と環同型。
方針：二つの一般完備化挿入比較を合成する。
規約：比較の両側の具体的な環構造を局所導入する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の既存候補へ平坦性を移す。 -/
def monicPrismaticPDPerfectionCandidateEquiv :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p x
    letI := polynomialPrismCommRing D d f
    H ≃+* T := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing (DeltaPerfection F) p (deltaPerfectionOf F 0 z)
  let := pdCompletionCommRing C p x
  let := polynomialPrismCommRing D d f
  exact (deltaPDCompletionPerfectionEquiv F z).symm.trans (deltaPerfectionPDCompletionEquiv F z)

/-- 概要：候補の環同型と逆同型は、実際の完備化 δ 構造と両立する。
方針：二つの一般完備化挿入比較の両方向の δ 射性を合成する。
規約：distinguished 性やモニック性を使わない一般環比較として述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の同じ完全 δ 候補への接続。 -/
theorem monicPrismaticPDPerfectionCandidateEquiv_isDeltaHom :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p x
    letI := pdCompletionCommRing (PCompletedDeltaPerfection F) p
      (pCompletedDeltaPerfectionMap F z)
    letI := polynomialPrismCommRing D d f
    (deltaPDCompletionStructure (deltaPerfectionStructure G) x).IsDeltaHom
      (deltaPDCompletionStructure (pCompletedDeltaPerfectionStructure F)
        (pCompletedDeltaPerfectionMap F z))
      (monicPrismaticPDPerfectionCandidateEquiv D d f).toRingHom ∧
    (deltaPDCompletionStructure (pCompletedDeltaPerfectionStructure F)
      (pCompletedDeltaPerfectionMap F z)).IsDeltaHom
      (deltaPDCompletionStructure (deltaPerfectionStructure G) x)
      (monicPrismaticPDPerfectionCandidateEquiv D d f).symm.toRingHom := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing (DeltaPerfection F) p (deltaPerfectionOf F 0 z)
  let := pdCompletionCommRing C p x
  let := pdCompletionCommRing (PCompletedDeltaPerfection F) p
    (pCompletedDeltaPerfectionMap F z)
  let := polynomialPrismCommRing D d f
  exact ⟨((deltaPerfectionPDCompletionEquiv_spec F z).1).comp
      (deltaPDCompletionPerfectionEquiv_spec F z).2.1,
    ((deltaPDCompletionPerfectionEquiv_spec F z).1).comp
      (deltaPerfectionPDCompletionEquiv_spec F z).2.1⟩

/-- 概要：候補比較は raw 包からの両標準射を保つ。
方針：一般比較の逆射と順射の標準 raw 射公式を順に使う。
規約：任意の raw 元で一致を確認する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A 作用の線形比較への入力。 -/
theorem monicPrismaticPDPerfectionCandidateEquiv_comp_raw :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p x
    letI := polynomialPrismCommRing D d f
    (monicPrismaticPDPerfectionCandidateEquiv D d f).toRingHom.comp r₀ =
      polynomialPrismRawMap D d f := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing (DeltaPerfection F) p (deltaPerfectionOf F 0 z)
  let := pdCompletionCommRing C p x
  let := polynomialPrismCommRing D d f
  apply RingHom.ext
  intro a
  have h : (deltaPDCompletionPerfectionEquiv F z).symm (r₀ a) =
      pdCompletionUnit (DeltaPerfection F) p (deltaPerfectionOf F 0 z)
        (deltaPerfectionOf F 0 a) :=
    RingHom.congr_fun (deltaPDCompletionPerfectionInverse_spec F z).2 a
  change deltaPerfectionPDCompletionEquiv F z
    ((deltaPDCompletionPerfectionEquiv F z).symm (r₀ a)) = polynomialPrismRawMap D d f a
  rw [h]
  exact RingHom.congr_fun (deltaPerfectionPDCompletionEquiv_spec F z).2.2 a

/-- 概要：候補の環同型は元の A の標準係数射を保つ。
方針：raw 係数射を保つ公式と合成の結合律を使う。
規約：係数射の取り替えを行わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の係数環に関する忠実平坦性の移送。 -/
theorem monicPrismaticPDPerfectionCandidateEquiv_comp_coefficient :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p x
    letI := polynomialPrismCommRing D d f
    (monicPrismaticPDPerfectionCandidateEquiv D d f).toRingHom.comp ((r₀).comp c) =
      polynomialPrismCoefficientMap D d f := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p x
  let := polynomialPrismCommRing D d f
  rw [← RingHom.comp_assoc, monicPrismaticPDPerfectionCandidateEquiv_comp_raw]
  rfl

/-- 概要：二つの候補の元の A 係数作用は、同じ環同型による線形同型を持つ。
方針：標準係数射を保つ公式と積の保存からスカラー作用の可換性を示す。
規約：元の係数環 A 上の同型を明示する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の既存候補の完全忠実平坦性。 -/
def monicPrismaticPDPerfectionCandidateModuleIso :
    letI := pdCompletionCommRing Raw p z
    letI := pdCompletionCommRing C p x
    letI := polynomialPrismCommRing D d f
    baseChangeScalarModule ((r₀).comp c) ≅
      baseChangeScalarModule (polynomialPrismCoefficientMap D d f) := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p x
  let := polynomialPrismCommRing D d f
  let e := monicPrismaticPDPerfectionCandidateEquiv D d f
  let M := baseChangeScalarModule ((r₀).comp c)
  let N := baseChangeScalarModule (polynomialPrismCoefficientMap D d f)
  let eA : M ≃ₗ[A] N :=
    { e.toAddEquiv with
      map_smul' := by
        intro a y
        change H at y
        change e ((r₀).comp c a * y) = polynomialPrismCoefficientMap D d f a * e y
        rw [map_mul]
        exact congrArg (fun h => h * e y)
          (RingHom.congr_fun (monicPrismaticPDPerfectionCandidateEquiv_comp_coefficient D d f) a) }
  exact eA.toModuleIso

end SerrePositivity.BhattScholze.Andre

end MonicPrismaticCandidateComparison

/-! ## モニック族の最初の実 δ 剰余関係の Koszul 分解

## 概要

任意モニック族の f/d 包の最初の δ 関係は、実 (p,d) 商で弱正則列をなす。
BS 著者版 Remark 7.15（著者版 p.62）の実導来剰余の離散性への入力。

## 方針

二重多項式係数商を展開し、d の像が零となることで各関係を負のモニック関係に移す。
原典の BS 著者版 Proposition 7.11 を使う証明とは異なる経路の計算。

## 規約

有限個の異なる添字を選ぶが、全添字型の有限性は要求しない。正次数も不要。

## 使われ方

一般 δ 除算の有限深さの既存弱正則性定理へ渡す。
-/

@[expose] public noncomputable section MonicPrismaticFirstResidueKoszul

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => (fun s : σ => monicRelation (f s) s)
local notation "K₀" => Ideal.span {(p : A), d}
local notation "KP₀" => Ideal.span {(p : P₀), MvPolynomial.C d}
local notation "KL₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}

/-- 概要：最初の実δ関係の異なる有限族は、実mod(p,d)商上で弱正則。
方針：二重係数商の表示で最初の関係を負のモニック関係族に移す。
規約：係数環の p 正則性や多項式の正次数は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の全有限 δ 深さへの初項入力。 -/
theorem monicPrismaticFirstRelation_mod_pd_fin_isWeaklyRegular
    (hf : ∀ s, (f s).Monic) {m : ℕ}
    (s : Fin m → σ) (hs : Function.Injective s) :
    RingTheory.Sequence.IsWeaklyRegular (L₀ ⧸ KL₀)
      (List.ofFn fun i => Ideal.Quotient.mk KL₀
        (deltaDivisionIteratedRelation E₀ (MvPolynomial.C d) c₀ (s i) 0)) := by
  have hP : (K₀).map (MvPolynomial.C : A →+* P₀) = KP₀ := by
    rw [Ideal.map_span]
    simp only [Set.image_pair, map_natCast]
  let eP := (Ideal.quotEquivOfEq hP.symm).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ) K₀).symm.toRingEquiv
  have heP (f : P₀) : eP (Ideal.Quotient.mk KP₀ f) =
      MvPolynomial.map (Ideal.Quotient.mk K₀) f := by
    dsimp only [eP]
    rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
    exact RingHom.congr_fun (monicPowerFamilyCoefficientQuotient_comp σ A K₀) f
  have hrP : RingTheory.Sequence.IsWeaklyRegular (P₀ ⧸ KP₀)
      (List.ofFn fun i => -Ideal.Quotient.mk KP₀ (c₀ (s i))) := by
    let rs := List.ofFn fun i => -Ideal.Quotient.mk KP₀ (c₀ (s i))
    refine (eP.toAddEquiv.isWeaklyRegular_congr (as := rs) (bs := rs.map eP) ?_).mpr ?_
    · apply List.forall₂_map_right_iff.mpr
      apply List.forall₂_same.mpr
      intro r _ x
      exact eP.map_mul r x
    · simpa only [rs, List.map_ofFn, Function.comp_def, map_neg, heP, monicRelation_map] using
        monicRelation_neg_fin_isWeaklyRegular
          (fun t => (f t).map (Ideal.Quotient.mk K₀))
          (fun t => (hf t).map (Ideal.Quotient.mk K₀)) s hs
  have hrL := hrP.of_flat (S := MvPolynomial (σ × ℕ) (P₀ ⧸ KP₀))
  have hL : (KP₀).map (MvPolynomial.C : P₀ →+* L₀) = KL₀ := by
    rw [Ideal.map_span]
    simp only [Set.image_pair, map_natCast]
  let eL := (Ideal.quotEquivOfEq hL.symm).trans
    (MvPolynomial.quotientEquivQuotientMvPolynomial (σ := σ × ℕ) KP₀).symm.toRingEquiv
  have heL (f : L₀) : eL (Ideal.Quotient.mk KL₀ f) =
      MvPolynomial.map (Ideal.Quotient.mk KP₀) f := by
    dsimp only [eL]
    rw [RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk]
    exact RingHom.congr_fun (monicPowerFamilyCoefficientQuotient_comp (σ × ℕ) P₀ KP₀) f
  have hd : Ideal.Quotient.mk KP₀ (MvPolynomial.C d) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr
      (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
  have he (t : σ) : eL (Ideal.Quotient.mk KL₀
      (deltaDivisionIteratedRelation E₀ (MvPolynomial.C d) c₀ t 0)) =
      -MvPolynomial.C (Ideal.Quotient.mk KP₀ (c₀ t)) := by
    rw [heL]
    change MvPolynomial.map (Ideal.Quotient.mk KP₀)
      (MvPolynomial.C (MvPolynomial.C d) * MvPolynomial.X (t, 0) - MvPolynomial.C (c₀ t)) = _
    rw [map_sub, map_mul, MvPolynomial.map_C, MvPolynomial.map_X, MvPolynomial.map_C,
      hd, map_zero, zero_mul, zero_sub]
  let rs := List.ofFn fun i => Ideal.Quotient.mk KL₀
    (deltaDivisionIteratedRelation E₀ (MvPolynomial.C d) c₀ (s i) 0)
  refine (eL.toAddEquiv.isWeaklyRegular_congr (as := rs) (bs := rs.map eL) ?_).mpr ?_
  · apply List.forall₂_map_right_iff.mpr
    apply List.forall₂_same.mpr
    intro r _ x
    exact eL.map_mul r x
  · simpa only [rs, List.map_ofFn, Function.comp_def, he, map_neg,
      MvPolynomial.algebraMap_eq] using hrL

/-- 概要：任意有限モニック族の最初の実残余Koszul複体は、対応する通常商の分解。
方針：二重係数商の表示で最初の関係を負のモニック関係族に移す。
規約：係数環の p 正則性や多項式の正次数は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の全有限 δ 深さへの初項入力。 -/
theorem monicPrismaticFirstRelation_mod_pd_fin_isKoszulResolution
    (hf : ∀ s, (f s).Monic) {m : ℕ}
    (s : Fin m → σ) (hs : Function.Injective s) :
    SerrePositivity.IsKoszulResolution (fun i => Ideal.Quotient.mk KL₀
      (deltaDivisionIteratedRelation E₀ (MvPolynomial.C d) c₀ (s i) 0)) :=
  SerrePositivity.isKoszulResolution_of_isWeaklyRegular _
    (monicPrismaticFirstRelation_mod_pd_fin_isWeaklyRegular D d f hf s hs)

end SerrePositivity.BhattScholze.Andre

end MonicPrismaticFirstResidueKoszul

/-! ## 有限モニック族の全有限 δ 深さの残余 Koszul 分解

## 概要

一般 f/d 包の実 (p,d) 商上で、有限モニック族の全有限 δ 深さの関係が Koszul 分解を与える。
BS 著者版 Remark 7.15（著者版 p.62）の実導来剰余の離散性への入力。

## 方針

最初の関係の弱正則性を一般 δ 除算の既存帰納へ渡し、評価関係へ移す。
原典の BS 著者版 Proposition 7.11 を使う経路とは異なる明示関係の計算。

## 規約

p 正則な係数環と δ(d) の単元性を仮定する。正次数は不要。

## 使われ方

実残余自由 δ 射に沿う全評価源の高次 Tor 消滅へ渡す。
-/

@[expose] public noncomputable section MonicPrismaticFiniteResidueKoszul

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
local notation "P₁" => MvPolynomial σ A
local notation "L₁" => RelativeFreeDeltaRing (R := P₁) σ
local notation "E₁" => polynomialRankOneDeltaStructure σ D
local notation "bRel" => (fun s : σ => monicRelation (f s) s)
local notation "K₁" => Ideal.span {(p : L₁), MvPolynomial.C (MvPolynomial.C d)}

/-- 概要：任意モニック関係族については、係数のp正則性とδd単元だけで全有限δ深さが弱正則。
方針：最初のモニック弱正則列を、一般 δ 除算の既存有限深さ定理に渡す。
規約：係数環の p 正則性と δ(d) の単元性を要求する。正次数は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実導来剰余の Tor 消滅入力。 -/
theorem monicPrismaticFiniteResidueFamilyList_isWeaklyRegular
    (hf : ∀ s, (f s).Monic) {m : ℕ} (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ) :
    RingTheory.Sequence.IsWeaklyRegular (L₁ ⧸ K₁)
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList E₁ (MvPolynomial.C d) bRel s N) := by
  have hpP : IsSMulRegular P₁ (p : P₁) := by
    simpa only [map_natCast] using
      (show IsSMulRegular A (p : A) from hpA).of_flat (S := P₁)
  have hpL : IsSMulRegular L₁ (p : L₁) := by
    simpa only [map_natCast] using hpP.of_flat (S := L₁)
  let vP := v.map (MvPolynomial.C : A →+* P₁).toMonoidHom
  have hvP : (vP : P₁) = (E₁).delta (MvPolynomial.C d) := by
    change MvPolynomial.C (v : A) = _
    rw [hv, polynomialRankOneDeltaStructure_delta_C]
  exact _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList_isWeaklyRegular E₁ (MvPolynomial.C d) bRel s
    hpP hpL (witt_ghostMap_injective_of_mul_prime_injective p L₁ hpL) vP hvP
    (monicPrismaticFirstRelation_mod_pd_fin_isWeaklyRegular D d f hf s s.injective) N

/-- 概要：有限モニック族の全有限δ深さの実mod(p,d)Koszul分解。
方針：最初のモニック弱正則列を、一般 δ 除算の既存有限深さ定理に渡す。
規約：係数環の p 正則性と δ(d) の単元性を要求する。正次数は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実導来剰余の Tor 消滅入力。 -/
theorem monicPrismaticFiniteResidueFamilyList_isKoszulResolution
    (hf : ∀ s, (f s).Monic) {m : ℕ} (s : Fin m ≃ σ)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) (N : ℕ) :
    SerrePositivity.IsKoszulResolution
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteResidueFamilyList E₁ (MvPolynomial.C d) bRel s N).get := by
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  simpa only [List.ofFn_get] using
    monicPrismaticFiniteResidueFamilyList_isWeaklyRegular D d f hf s hpA v hv N


variable {m : ℕ} (s : Fin m ≃ σ) (N : ℕ)
local notation "cs" => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates (s : Fin m → σ) N
local notation "q₁" => Ideal.Quotient.mk K₁
local notation "α₁" => deltaDivisionSourceMap (σ := σ) E₁ (MvPolynomial.C d)

/-- 概要：全有限 δ 座標の実残余評価関係は Koszul 分解を与える。
方針：残余関係リストの弱正則性を既存の評価リストの弱正則性へ渡す。
規約：有限添字型の全列挙を明示する。正次数は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の残余自由 δ 射に沿う源商の Tor 消滅。 -/
theorem monicPrismaticFiniteResidueEvaluationFamily_isKoszulResolution
    (hf : ∀ s, (f s).Monic)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    SerrePositivity.IsKoszulResolution (fun i : Fin (cs).length =>
      q₁ (deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) bRel
        ((cs).get i).1 ((cs).get i).2)) := by
  let g : σ × ℕ → L₁ ⧸ K₁ := fun z =>
    q₁ (deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) bRel z.1 z.2)
  change SerrePositivity.IsKoszulResolution (g ∘ (cs).get)
  apply SerrePositivity.isKoszulResolution_of_isWeaklyRegular
  rw [← List.map_ofFn, List.ofFn_get]
  exact _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteEvaluationFamilyList_isWeaklyRegular E₁ (MvPolynomial.C d) bRel s
    (fun k => monicPrismaticFiniteResidueFamilyList_isWeaklyRegular D d f hf s hpA v hv k) N

/-- 概要：有限モニック族の全有限 δ 深さの源グラフ商は、残余自由 δ 射に沿う高次 Tor が零。
方針：源グラフの Koszul 分解を実残余評価 Koszul ホモロジーへ移し、消滅を適用する。
規約：実射は一般除算源射と実 (p,d) 商射の合成で固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の全深さ評価源の離散性への有限段入力。 -/
theorem monicPrismaticFiniteResidueEvaluationFamilySource_tor_subsingleton
    (hf : ∀ s, (f s).Monic)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) (i : ℕ) :
    Subsingleton (SerrePositivity.TorAlg ((q₁).comp α₁) (i + 1)
      (_root_.SerrePositivity.BhattScholze.Andre.DeltaDivisionSourceFiniteCoordinateQuotient E₁ bRel (cs).get)) := by
  have e := SerrePositivity.torAlgKoszulIso ((q₁).comp α₁)
    (fun j : Fin (cs).length => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraphRelation E₁ bRel ((cs).get j))
    (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraph_fin_isKoszulResolution E₁ bRel (cs).get
      (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionFiniteFamilyCoordinates_nodup s s.injective N).injective_get) (i + 1)
  have he : ((q₁).comp α₁) ∘
      (fun j : Fin (cs).length => _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraphRelation E₁ bRel ((cs).get j)) =
      (fun j : Fin (cs).length => q₁ (deltaDivisionEvaluationRelation E₁ (MvPolynomial.C d) bRel
        ((cs).get j).1 ((cs).get j).2)) := by
    funext j
    exact congrArg q₁ (_root_.SerrePositivity.BhattScholze.Andre.deltaDivisionSourceGraph_map E₁ (MvPolynomial.C d) bRel ((cs).get j))
  rw [he] at e
  have hr := monicPrismaticFiniteResidueEvaluationFamily_isKoszulResolution D d f s N hf hpA v hv
  exact ModuleCat.subsingleton_of_isZero ((hr.isZero (-((i + 1 : ℕ) : ℤ)) (by omega)).of_iso e)

end SerrePositivity.BhattScholze.Andre

end MonicPrismaticFiniteResidueKoszul

/-! ## 有限モニック族の実残余導来評価比較

## 概要

有限モニック族について、一般 f/d 包の実残余自由 δ 源の導来評価は実 raw 剰余の single に同型。
BS 著者版 Remark 7.15（著者版 p.62）の実導来剰余比較の評価側。

## 方針

各有限 δ 深さの Koszul Tor 消滅を既存 余極限との比較 に渡し、Tor 対称性と標準 augmentation で比較する。
原典の BS 著者版 Proposition 7.11 を使う経路とは異なる明示関係による計算。

## 規約

元の係数環への制限や完備化後の主張は含まない。正次数は不要。

## 使われ方

一般 f/d 包の実係数側導来還元と実 raw (p,d) 商との比較に接続する。
-/

@[expose] public noncomputable section MonicPrismaticSourceResidue

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits
open scoped _root_.TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
variable {m : ℕ} (s : Fin m ≃ σ)
local notation "P₁" => MvPolynomial σ A
local notation "L₁" => RelativeFreeDeltaRing (R := P₁) σ
local notation "E₁" => polynomialRankOneDeltaStructure σ D
local notation "c₁" => (fun t : σ => monicRelation (f t) t)
local notation "K₁" => Ideal.span {(p : L₁), MvPolynomial.C (MvPolynomial.C d)}
local notation "ψ₁" => RingHom.comp (Ideal.Quotient.mk K₁)
  (deltaDivisionSourceMap (σ := σ) E₁ (MvPolynomial.C d))

include s in
/-- 概要：有限モニック添字について、実残余自由δ射に沿う全β評価環の正次数Torが零。
方針：有限 δ 深さの Tor 消滅を既存の逐次余極限と Tor 対称性で移す。
規約：有限添字型を明示的な全列挙で与える。正次数は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の標準導来 augmentation の入力。 -/
theorem monicPrismaticResidueSource_tor_subsingleton
    (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) (i : ℕ) :
    letI := deltaDivisionSourceEvaluationAlgebra E₁ c₁
    Subsingleton (SerrePositivity.TorAlg ψ₁ (i + 1) P₁) := by
  let := deltaDivisionSourceEvaluationAlgebra E₁ c₁
  apply _root_.SerrePositivity.BhattScholze.Andre.deltaDivisionEvaluationSourceFamily_tor_subsingleton E₁ c₁ s ψ₁ i
  intro N
  exact monicPrismaticFiniteResidueEvaluationFamilySource_tor_subsingleton D d f s N hf hpA v hv i

local notation "β₁" => deltaDivisionSourceEval E₁ c₁
local notation "Mψ" => baseChangeScalarModule ψ₁
local notation "Mβ" => baseChangeScalarModule β₁

include s in
/-- 概要：Tor対称性で、同じ実残余終域をβに沿って導来拡大するための消滅条件を得る。
方針：有限 δ 深さの Tor 消滅を既存の逐次余極限と Tor 対称性で移す。
規約：有限添字型を明示的な全列挙で与える。正次数は不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の標準導来 augmentation の入力。 -/
theorem monicPrismaticResidueSourceEval_torVanishing
    (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    scalarExtensionTorVanishing β₁ Mψ := by
  intro n hn
  cases n with
  | zero => exact (Nat.lt_irrefl 0 hn).elim
  | succ i =>
      let := deltaDivisionSourceEvaluationAlgebra E₁ c₁
      let : Subsingleton (((ModuleCat.extendScalars ψ₁).leftDerived (i + 1)).obj Mβ) :=
        monicPrismaticResidueSource_tor_subsingleton
          (D := D) (f := f) (s := s) (d := d) hf hpA v hv i
      have hz : IsZero (((ModuleCat.extendScalars ψ₁).leftDerived (i + 1)).obj Mβ) :=
        ModuleCat.isZero_of_subsingleton _
      have hH := (derivedModuleBaseChangeHomologyIso ψ₁ (i + 1)).app Mβ
      have hzH := hH.isZero_iff.mpr hz
      have hzR := (ModuleCat.restrictScalars ψ₁).map_isZero hzH
      have hzT := ((derivedModuleBaseChangeTorIso ψ₁ (i + 1)).app Mβ).isZero_iff.mp hzR
      exact ((torComm (i + 1) Mβ Mψ).toModuleIso).isZero_iff.mpr hzT


local notation "Q₁" => L₁ ⧸ K₁
local notation "Res₁" => DeltaAdjoinDivisionResidue E₁ (MvPolynomial.C d) c₁

/-- 概要：有限モニック族の実残余終域の導来評価は raw (p,d) 商の次数零対象と標準同型。
方針：高次 Tor 消滅による標準 augmentation と、通常残余テンソルの既存同型を合成する。
規約：同じ元の自由 δ 源射と評価射を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の係数側の実導来剰余比較。 -/
def monicPrismaticResidueSourceDerivedIso
    (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun z : A => (p : A) * z))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    (boundedAboveDerivedBaseChange β₁).obj (boundedAboveDerivedSingleFunctor.obj Mψ) ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₁ Res₁) := by
  letI := deltaDivisionSourceEvaluationAlgebra E₁ c₁
  letI := deltaDivisionSourceResidueTargetAlgebra (σ := σ) E₁ (MvPolynomial.C d)
  letI : Module L₁ Q₁ := Algebra.toModule
  let e₁ : ((ModuleCat.extendScalars β₁).obj Mψ) ≃ₗ[P₁] (P₁ ⊗[L₁] Q₁) :=
    { toFun := fun z => z
      invFun := fun z => z
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  let e := e₁.trans
    (deltaDivisionSourceResidueTensorAlgEquiv E₁ (MvPolynomial.C d) c₁).toLinearEquiv
  exact boundedAboveDerivedBaseChangeModuleAugmentationIso β₁ Mψ
    (monicPrismaticResidueSourceEval_torVanishing D d f s hf hpA v hv) ≪≫
      boundedAboveDerivedSingleFunctor.mapIso e.toModuleIso

end SerrePositivity.BhattScholze.Andre

end MonicPrismaticSourceResidue

/-! ## モニック族の係数側の実導来剰余比較

## 概要

有限モニック族の f/d 包の自由 δ 源上の実三因子還元は、実 raw (p,d) 剰余の single に同型。
BS 著者版 Remark 7.15（著者版 p.62）の元の係数環への比較の準備。

## 方針

既存の一般結合子と右因子の商比較、前工程の標準導来評価比較を合成する。
原典の BS 著者版 Proposition 7.11 を使う証明とは異なる実関係による計算。

## 規約

正次数は不要。元の係数作用を保つ具体的な導来同型を構成する。

## 使われ方

実自由 δ 源の商上へ作用を降下し、元の A/(p,d) 上でのホモロジーを計算する。
-/

@[expose] public noncomputable section MonicPrismaticCoefficientReduction

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A) {m : ℕ}
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => (fun t : σ => monicRelation (f t) t)
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "q₀" => Ideal.Quotient.mk K₀
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "β₀" => deltaDivisionSourceEval E₀ c₀
local notation "ψ₀" => RingHom.comp q₀ α₀
local notation "Mα" => baseChangeScalarModule α₀
local notation "Mβ" => baseChangeScalarModule β₀
local notation "Mψ" => baseChangeScalarModule ψ₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀
local notation "MRes" => CategoryTheory.Functor.obj
  (ModuleCat.restrictScalars β₀) (ModuleCat.of P₀ Res₀)

/-- 概要：一般モニック f/d 包の自由 δ 源上の三因子導来還元対象。
方針：評価・除算の二因子導来テンソルを実 (p,d) 商のスカラー対象とテンソルする。
規約：導来還元の実対象を明示する。平坦性は定義に含めない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実商還元を raw 剰余へ比較する。 -/
abbrev MonicPrismaticSourceCoefficientReduced :=
  boundedAboveDerivedTensor.obj
    (boundedAboveDerivedTensor.obj
      (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα),
        derivedBaseChangeScalarObject q₀)

/-- 概要：有限モニック族について、係数商による実三因子還元は既存raw(p,d)商の次数零対象に一致する。
方針：一般の結合子比較と標準導来評価比較を合成する。
規約：有限全列挙、モニック性、係数環の p 正則性、δ(d) の単元性を仮定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の係数商への実還元。 -/
def monicPrismaticSourceCoefficientResidueIso (s : Fin m ≃ σ) (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    MonicPrismaticSourceCoefficientReduced D d f ≅ boundedAboveDerivedSingleFunctor.obj MRes := by
  let e₁ := deltaDivisionSourceResidueAssociatorReductionIso E₀ (MvPolynomial.C d) c₀
  let e₂ := (boundedAboveDerivedBaseChangeTensorIso β₀
    (boundedAboveDerivedSingleFunctor.obj Mψ)).symm
  let e₃ := (boundedAboveDerivedRestrictScalars β₀).mapIso
    (monicPrismaticResidueSourceDerivedIso D d f s hf hpA v hv)
  let e₄ : (boundedAboveDerivedRestrictScalars β₀).obj
      (boundedAboveDerivedSingleFunctor.obj (ModuleCat.of P₀ Res₀)) ≅
        boundedAboveDerivedSingleFunctor.obj MRes :=
    ObjectProperty.isoMk _
      ((derivedRestrictScalarsSingleIso β₀ 0).app (ModuleCat.of P₀ Res₀))
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ e₄

/-- 概要：実係数還元のH0は、βによる実源作用を持つ既存raw残余商と加群同型。
方針：一般の結合子比較と標準導来評価比較を合成する。
規約：有限全列挙、モニック性、係数環の p 正則性、δ(d) の単元性を仮定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の係数商への実還元。 -/
def monicPrismaticSourceCoefficientResidueHomologyZeroIso (s : Fin m ≃ σ) (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    ((DerivedCategory.homologyFunctor (ModuleCat L₀) 0).obj
      (MonicPrismaticSourceCoefficientReduced D d f).obj) ≅ MRes :=
  (((DerivedCategory.homologyFunctor (ModuleCat L₀) 0).mapIso
    (DerivedCategory.Minus.ι.mapIso
      (monicPrismaticSourceCoefficientResidueIso D d f s hf hpA v hv))) ≪≫
        (realizedSingleH0Iso L₀).app MRes)

/-- 概要：実係数商還元の非零次数ホモロジーは、同じ明示入力の下で零。
方針：一般の結合子比較と標準導来評価比較を合成する。
規約：有限全列挙、モニック性、係数環の p 正則性、δ(d) の単元性を仮定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の係数商への実還元。 -/
theorem monicPrismaticSourceCoefficientResidue_homology_isZero
    (s : Fin m ≃ σ) (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat L₀) i).obj
      (MonicPrismaticSourceCoefficientReduced D d f).obj) :=
  (derivedSingleHomology_isZero MRes i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat L₀) i).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (monicPrismaticSourceCoefficientResidueIso D d f s hf hpA v hv)))

end SerrePositivity.BhattScholze.Andre

end MonicPrismaticCoefficientReduction

/-! ## モニック族の実自由 δ 源商上の導来還元

## 概要

有限モニック族の実導来還元は、作用を降下した raw (p,d) 剰余の single と同型。
BS 著者版 Remark 7.15（著者版 p.62）の実係数商への比較。

## 方針

自由 δ 源から商への全射性で H⁰ の線形比較を降下し、ホモロジー消滅と正規化純対象比較を使う。
原典の BS 著者版 Proposition 7.11 を用いる証明とは異なる実関係による計算。

## 規約

有限全列挙とモニック性、p 正則性、δ(d) の単元性を仮定する。正次数は不要。

## 使われ方

元の係数環の (p,d) 商へ制限して、実導来剰余の忠実平坦性へ接続する。
-/

@[expose] public noncomputable section MonicPrismaticQuotientDerived

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
open _root_.CategoryTheory _root_.CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => (fun t : σ => monicRelation (f t) t)
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q₀" => L₀ ⧸ K₀
local notation "q₀" => Ideal.Quotient.mk K₀
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "β₀" => deltaDivisionSourceEval E₀ c₀
local notation "ψ₀" => RingHom.comp q₀ α₀
local notation "Mα" => baseChangeScalarModule α₀
local notation "Mβ" => baseChangeScalarModule β₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀
local notation "MRes" => CategoryTheory.Functor.obj
  (ModuleCat.restrictScalars β₀) (ModuleCat.of P₀ Res₀)
local notation "j₀" => deltaAdjoinDivisionMap E₀ (MvPolynomial.C d) c₀
local notation "r₀" => Ideal.Quotient.mk
  (deltaAdjoinDivisionResidueIdeal E₀ (MvPolynomial.C d) c₀)

/-- 概要：実二因子導来テンソルを実商環Q上へ基底変更した対象。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
abbrev MonicPrismaticSourceQuotientDerived :=
  (boundedAboveDerivedBaseChange q₀).obj
    (boundedAboveDerivedTensor.obj
      (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα))

/-- 概要：raw残余商上のβを経由する源作用の、実商環への標準降下。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
def monicPrismaticSourceQuotientResidueMap : Q₀ →+* Res₀ :=
  Ideal.Quotient.lift K₀ ((r₀).comp ((j₀).comp β₀)) (by
    change K₀ ≤ RingHom.ker ((r₀).comp ((j₀).comp β₀))
    apply Ideal.span_le.mpr
    intro x hx
    rcases Set.mem_insert_iff.mp hx with hx | hx
    · subst x
      change r₀ ((j₀).comp β₀ (p : L₀)) = 0
      rw [map_natCast]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_insert _ _))
    · have hx := Set.mem_singleton_iff.mp hx
      subst x
      change r₀ (j₀ (β₀ (MvPolynomial.C (MvPolynomial.C d)))) = 0
      rw [deltaDivisionSourceEval_C]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr
        (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))))

/-- 概要：商代表元の作用は、β、raw係数射、残余商射の合成である。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
theorem monicPrismaticSourceQuotientResidueMap_mk (x : L₀) :
    monicPrismaticSourceQuotientResidueMap D d f (q₀ x) = r₀ (j₀ (β₀ x)) := rfl

/-- 概要：商環作用をqで制限すると、前工程のβによる実L加群になる。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
def monicPrismaticSourceQuotientResidueRestrictionIso :
    letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    ((ModuleCat.restrictScalars q₀).obj (ModuleCat.of Q₀ Res₀)) ≅ MRes := by
  letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact
    { hom := { hom' :=
        { toFun := fun x => x
          map_add' := fun _ _ => rfl
          map_smul' := fun r x => by
            change Res₀ at x
            change r₀ (j₀ (β₀ r)) * x = (β₀ r) • x
            rw [Algebra.smul_def]
            rfl } }
      inv := { hom' :=
        { toFun := fun x => x
          map_add' := fun _ _ => rfl
          map_smul' := fun r x => by
            change Res₀ at x
            change (β₀ r) • x = r₀ (j₀ (β₀ r)) * x
            rw [Algebra.smul_def]
            rfl } }
      hom_inv_id := by rfl
      inv_hom_id := by rfl }

/-- 概要：実商環上の基底変更を制限すると、既存の実三因子還元に一致する。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
def monicPrismaticSourceQuotientDerivedRestrictionIso :
    (boundedAboveDerivedRestrictScalars q₀).obj
        (MonicPrismaticSourceQuotientDerived D d f) ≅
      MonicPrismaticSourceCoefficientReduced D d f :=
  (boundedAboveDerivedBaseChangeRightTensorNatIso q₀).app _


variable {m : ℕ}
/-- 概要：実商環上の還元のホモロジーを制限した対象と、raw残余商とのH0同型。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
def monicPrismaticSourceQuotientDerivedRestrictedH0Iso (s : Fin m ≃ σ) (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    (ModuleCat.restrictScalars q₀).obj
      ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
        (MonicPrismaticSourceQuotientDerived D d f).obj) ≅ MRes :=
  ((derivedRestrictScalarsHomologyIso q₀ 0).app
      (MonicPrismaticSourceQuotientDerived D d f).obj).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat L₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso (monicPrismaticSourceQuotientDerivedRestrictionIso D d f)) ≪≫
    monicPrismaticSourceCoefficientResidueHomologyZeroIso
      D d f s hf hpA v hv

/-- 概要：有限モニック族について、実商環上の還元そのものの非零次数ホモロジーが消える。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
theorem monicPrismaticSourceQuotientDerived_homology_isZero
    (s : Fin m ≃ σ) (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj
      (MonicPrismaticSourceQuotientDerived D d f).obj) := by
  have hz := monicPrismaticSourceCoefficientResidue_homology_isZero
    D d f s hf hpA v hv i hi
  have hz' := hz.of_iso ((DerivedCategory.homologyFunctor (ModuleCat L₀) i).mapIso
    (DerivedCategory.Minus.ι.mapIso (monicPrismaticSourceQuotientDerivedRestrictionIso D d f)))
  have hr := (derivedRestrictScalarsHomologyIso q₀ i).app
    (MonicPrismaticSourceQuotientDerived D d f).obj
  have hs := hr.isZero_iff.mp hz'
  let : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat Q₀) i).obj
      (MonicPrismaticSourceQuotientDerived D d f).obj) :=
    ModuleCat.subsingleton_of_isZero (R := L₀) hs
  exact ModuleCat.isZero_of_subsingleton _

/-- 概要：実商環上でのH0同型。qの全射性により、L線形比較を実Q線形比較へ昇格する。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
def monicPrismaticSourceQuotientDerivedH0Iso (s : Fin m ≃ σ) (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
      (MonicPrismaticSourceQuotientDerived D d f).obj) ≅ ModuleCat.of Q₀ Res₀ := by
  letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  let e := monicPrismaticSourceQuotientDerivedRestrictedH0Iso
    D d f s hf hpA v hv ≪≫ (monicPrismaticSourceQuotientResidueRestrictionIso D d f).symm
  refine
    { hom := { hom' :=
        { toFun := e.hom.hom
          map_add' := e.hom.hom.map_add
          map_smul' := ?_ } }
      inv := { hom' :=
        { toFun := e.inv.hom
          map_add' := e.inv.hom.map_add
          map_smul' := ?_ } }
      hom_inv_id := ?_
      inv_hom_id := ?_ }
  · intro s x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
    have h := e.hom.hom.map_smul r x
    change e.hom.hom ((q₀ r) • x) = (q₀ r) • e.hom.hom x at h
    exact h
  · intro s x
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
    have h := e.inv.hom.map_smul r x
    change e.inv.hom ((q₀ r) • x) = (q₀ r) • e.inv.hom x at h
    exact h
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f => f.hom x) e.hom_inv_id
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact congrArg (fun f => f.hom x) e.inv_hom_id

local notation "X₀" => MonicPrismaticSourceQuotientDerived D d f

/-- 概要：有限モニック族の実商還元は、標準t構造の非負部分に属する。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
theorem monicPrismaticSourceQuotientDerived_isGE_zero
    (s : Fin m ≃ σ) (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    DerivedCategory.IsGE (X₀).obj 0 := by
  apply (DerivedCategory.isGE_iff _ _).mpr
  intro i hi
  exact monicPrismaticSourceQuotientDerived_homology_isZero
    D d f s hf hpA v hv i (by omega)

/-- 概要：同じ入力の下で標準t構造の非正部分にも属する。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
theorem monicPrismaticSourceQuotientDerived_isLE_zero
    (s : Fin m ≃ σ) (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    DerivedCategory.IsLE (X₀).obj 0 := by
  apply (DerivedCategory.isLE_iff _ _).mpr
  intro i hi
  exact monicPrismaticSourceQuotientDerived_homology_isZero
    D d f s hf hpA v hv i (by omega)

/-- 概要：実Q上の還元対象は、作用を降下した既存raw残余商の次数零対象と同型。
方針：実商射の全射性と係数制限のホモロジー比較で、前工程の具体的比較を商作用へ降下する。
規約：構成する各作用は元の自由 δ 源射を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A/(p,d) 上への比較。 -/
def monicPrismaticSourceQuotientDerivedSingleIso (s : Fin m ≃ σ) (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    X₀ ≅ boundedAboveDerivedSingleFunctor.obj (ModuleCat.of Q₀ Res₀) := by
  letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  have := monicPrismaticSourceQuotientDerived_isGE_zero D d f s hf hpA v hv
  have := monicPrismaticSourceQuotientDerived_isLE_zero D d f s hf hpA v hv
  exact ObjectProperty.isoMk _ (normalizedPureHomologyIso (X₀).obj 0) ≪≫
    boundedAboveDerivedSingleFunctor.mapIso
      (monicPrismaticSourceQuotientDerivedH0Iso D d f s hf hpA v hv)


end SerrePositivity.BhattScholze.Andre

end MonicPrismaticQuotientDerived

/-! ## 多項式 prism 候補の標準基底射

## 概要

多項式族の既存台環候補を完全 prism として束ね、元の係数射が生成元とイデアルを保つことを示す。
BS 著者版 Remark 7.15（著者版 p.62）の perfectoid 商の実係数射の準備。

## 方針

一般除算候補の完全 prism を使い、標準 δ 射を合成する。商射は代表元で比較する。
原典の BS 著者版 Proposition 7.11 を使う証明とは異なる具体的係数射による計算。

## 規約

任意多項式族を扱い、モニック性・正次数・有限性を要求しない。

## 使われ方

生成元の正則性と実生成元商の標準 perfectoid 候補への比較に使う。
-/

@[expose] public noncomputable section MonicPrismaticPrismBaseMap

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun t : σ => monicRelation (f t) t)
local notation "F" => deltaAdjoinDivisionStructure E (MvPolynomial.C d) r
local notation "T" => DivisionPrismCarrier E (MvPolynomial.C d) r
local notation "W" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.PCompletedDeltaDivision E (MvPolynomial.C d) r
local notation "j" => _root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionMap E (MvPolynomial.C d) r

/-- 概要：既存多項式候補台環を、選択生成元を持つ prism として束ねる。
方針：一般関係族の除算候補を独立変数の評価族に適用する。
規約：係数環の d の distinguished 性を明示する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の標準 perfectoid 商の基底射。 -/
def polynomialPrism (hd : D.IsDistinguished d) :
    letI := polynomialPrismCommRing D d f
    OrientedPrism p T := by
  let := polynomialPrismCommRing D d f
  exact divisionPrism E (MvPolynomial.C d) r
    ((polynomialRankOneDeltaStructure_C_isDeltaHom σ D).map_isDistinguished hd)

/-- 概要：既存多項式 prism 候補の δ 構造は完全。
方針：一般関係族の完全 prism 構成の既存結果を使う。
規約：多項式族の平坦性を仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の商の perfectoid 性と生成元の比較。 -/
theorem polynomialPrism_isPerfect (hd : D.IsDistinguished d) :
    letI := polynomialPrismCommRing D d f
    (polynomialPrism D d f hd).deltaStructure.IsPerfect := by
  let := polynomialPrismCommRing D d f
  exact divisionPrism_isPerfect E (MvPolynomial.C d) r
    ((polynomialRankOneDeltaStructure_C_isDeltaHom σ D).map_isDistinguished hd)

/-- 概要：raw 包から候補台環への標準射は δ 射。
方針：p 進完備 δ 完全化と実 PD 完備化単位の δ 射性を合成する。
規約：任意多項式族を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の候補の標準係数射を prism 射にする。 -/
theorem polynomialPrismRawMap_isDeltaHom (hd : D.IsDistinguished d) :
    letI := polynomialPrismCommRing D d f
    (F).IsDeltaHom (polynomialPrism D d f hd).deltaStructure (polynomialPrismRawMap D d f) := by
  let := polynomialPrismCommRing D d f
  exact (pdCompletionUnit_isDeltaHom (_root_.SerrePositivity.BhattScholze.Semiperfectoid.pCompletedDeltaDivisionStructure E (MvPolynomial.C d) r)
    (j (MvPolynomial.C d))).comp (pCompletedDeltaPerfectionMap_isDeltaHom F)

/-- 概要：元の A から候補への標準係数射は δ 射。
方針：多項式係数包含、raw 除算射、候補射の δ 射性を合成する。
規約：係数射は前工程の具体的な標準射である。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の標準 prism 射。 -/
theorem polynomialPrismCoefficientMap_isDeltaHom (hd : D.IsDistinguished d) :
    letI := polynomialPrismCommRing D d f
    D.IsDeltaHom (polynomialPrism D d f hd).deltaStructure (polynomialPrismCoefficientMap D d f) := by
  let := polynomialPrismCommRing D d f
  exact (polynomialPrismRawMap_isDeltaHom D d f hd).comp
    ((deltaAdjoinDivisionMap_isDeltaHom E (MvPolynomial.C d) r).comp
      (polynomialRankOneDeltaStructure_C_isDeltaHom σ D))

/-- 概要：元の d の像は候補 prism の選択生成元そのもの。
方針：標準係数射と候補生成元の定義の一致による。
規約：任意多項式族を扱う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の生成元商の比較。 -/
theorem polynomialPrismCoefficientMap_generator (hd : D.IsDistinguished d) :
    letI := polynomialPrismCommRing D d f
    polynomialPrismCoefficientMap D d f d = (polynomialPrism D d f hd).generator := rfl

/-- 概要：元の生成元イデアルの標準像は候補 prism のイデアル全体に一致する。
方針：主イデアルの像と生成元の標準像を使う。
規約：イデアルの包含だけでなく等式を示す。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の標準 perfectoid 商の同定。 -/
theorem polynomialPrismCoefficientMap_ideal (hd : D.IsDistinguished d) :
    letI := polynomialPrismCommRing D d f
    (Ideal.span {d}).map (polynomialPrismCoefficientMap D d f) =
      (polynomialPrism D d f hd).ideal := by
  let := polynomialPrismCommRing D d f
  rw [Ideal.map_span, Set.image_singleton, polynomialPrismCoefficientMap_generator D d f hd]
  rfl

/-- 概要：標準係数射による候補台環の A 代数構造。
方針：具体的係数射の toAlgebra を使う。
規約：利用箇所で局所導入する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の通常生成元商の係数作用。 -/
@[instance_reducible] def polynomialPrismCoefficientAlgebra :
    letI := polynomialPrismCommRing D d f
    Algebra A T := by
  let := polynomialPrismCommRing D d f
  exact (polynomialPrismCoefficientMap D d f).toAlgebra

/-- 概要：元の prism から既存多項式 prism 候補への標準 prism 射。
方針：標準係数 δ 射と生成元イデアルの像の等式を束ねる。
規約：基底 prism の生成元の distinguished 性を明示する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の perfectoid 商の基底射。 -/
def polynomialPrismBaseHom (P : OrientedPrism p A)
    (hd : P.deltaStructure.IsDistinguished P.generator) (f : σ → Polynomial A) :
    letI := polynomialPrismCommRing P.deltaStructure P.generator f
    OrientedPrism.Hom P (polynomialPrism P.deltaStructure P.generator f hd) := by
  let := polynomialPrismCommRing P.deltaStructure P.generator f
  refine ⟨polynomialPrismCoefficientMap P.deltaStructure P.generator f,
    polynomialPrismCoefficientMap_isDeltaHom P.deltaStructure P.generator f hd, ?_⟩
  apply Ideal.map_le_iff_le_comap.mp
  change (Ideal.span {P.generator}).map _ ≤ _
  exact (polynomialPrismCoefficientMap_ideal P.deltaStructure P.generator f hd).le

/-- 概要：標準 prism 射の誘導商射は既存 perfectoid 候補の基底射と一致する。
方針：元の生成元商の代表元で比較する。
規約：同じ候補への具体的な二つの係数射を照合する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の perfectoid 商の p 完全忠実平坦性。 -/
theorem polynomialPrismBaseHom_quotientMap (P : OrientedPrism p A)
    (hd : P.deltaStructure.IsDistinguished P.generator) (f : σ → Polynomial A) :
    letI := polynomialPrismCommRing P.deltaStructure P.generator f
    (polynomialPrismBaseHom P hd f).quotientMap =
      polynomialPerfectoidCandidateBaseMap P.deltaStructure P.generator f hd := by
  let := polynomialPrismCommRing P.deltaStructure P.generator f
  apply RingHom.ext
  intro y
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective y
  rfl

end SerrePositivity.BhattScholze.Andre

end MonicPrismaticPrismBaseMap
