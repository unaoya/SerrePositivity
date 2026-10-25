module

public import SerrePositivity.BhattScholze.Prism.Perfection.PCompletedDeltaDivision
public import SerrePositivity.BhattScholze.Prism.Perfection.PerfectDeltaPDPrism
public import SerrePositivity.BhattScholze.Prism.Perfectoid.PerfectPrismQuotientPerfectoid

/-!
# André E1：任意関係族の δ 除算による perfectoid 候補

## 概要

distinguished 元 d を持つ δ 環で、任意の元族 a を d で除算し、完全化した完全 prism の
商を構成する。商では d と各 a の像が零になる。
BS 著者版 Prop 3.13（pp.33–35）、Thm 7.14（p.61）、Rem 7.15（p.62）に対応する候補である。

## 方針

B4-6 の候補構成のうち、冪根関係の形に依存しない部分を一般の元族で再構成する。
既存の p 進完備 δ 完全化と実導来 (p,d) 完備化を使う。
原典の Prop 7.11 を使う証明とは異なる経路の構成部分である。

## 規約

元族の正則性や商の非零性を仮定せず、候補が零環になる場合も許す。
基底射の平坦性・忠実性はこのファイルでは証明しない。

## 使われ方

任意モニック多項式を独立変数で評価した元族を入力し、根方程式と perfectoid 性を保持する。
-/

@[expose] public noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

open SerrePositivity.DerivedCompletion

variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A)

local notation "C" => PCompletedDeltaDivision D d a
local notation "j" => pCompletedDeltaDivisionMap D d a
local notation "E" => pCompletedDeltaDivisionStructure D d a

/-- 概要：任意関係族を除算した完全 δ 環の実 (p,d) 完備化の台集合。
方針：既存の実完備化 H⁰ を使う。
規約：環構造は `divisionPrismCommRing` で明示する。
使われ方：BS Prop 3.13（著者版 pp.33–35）の候補構成部分。 -/
abbrev DivisionPrismCarrier := PDCompletionH0 C p (j d)

/-- 概要：実 H⁰ の既存可換環構造を候補に入れる。
方針：`pdCompletionCommRing` を使用する。
規約：明示的に局所導入する。
使われ方：BS Prop 3.13（著者版 pp.33–35）の候補。 -/
@[instance_reducible] def divisionPrismCommRing : CommRing (DivisionPrismCarrier D d a) :=
  pdCompletionCommRing C p (j d)

/-- 概要：任意の関係族から完全 prism 候補を構成する。
方針：distinguished 性を δ 射で移し、完全 δ 環の実完備化定理を適用する。
規約：忠実平坦性を結論しない。
使われ方：BS Thm 7.14（著者版 p.61）の別経路の一段候補。 -/
def divisionPrism (hd : D.IsDistinguished d) :
    letI := divisionPrismCommRing D d a
    OrientedPrism p (DivisionPrismCarrier D d a) := by
  let := divisionPrismCommRing D d a
  exact perfectDeltaPDPrism E (pCompletedDeltaDivision_isPerfect D d a) (j d)
    ((pCompletedDeltaDivisionMap_isDeltaHom D d a).map_isDistinguished hd)

/-- 概要：構成した候補 prism の δ 構造は完全。
方針：完全 δ 環の実完備化についての既存定理を適用する。
規約：任意元族を扱う。
使われ方：BS Thm 7.14（著者版 p.61）の perfectoid 商を得る。 -/
theorem divisionPrism_isPerfect (hd : D.IsDistinguished d) :
    letI := divisionPrismCommRing D d a
    (divisionPrism D d a hd).deltaStructure.IsPerfect := by
  let := divisionPrismCommRing D d a
  exact perfectDeltaPDPrism_isPerfect E (pCompletedDeltaDivision_isPerfect D d a) (j d)
    ((pCompletedDeltaDivisionMap_isDeltaHom D d a).map_isDistinguished hd)

/-- 概要：完全 prism 候補の標準商を perfectoid 候補とする。
方針：prism の定義イデアルで割る。
規約：零環を許す。
使われ方：BS Thm 7.14（著者版 p.61）の根付き拡大の台環の候補。 -/
abbrev DivisionPerfectoidCandidate (hd : D.IsDistinguished d) :=
  letI := divisionPrismCommRing D d a
  DivisionPrismCarrier D d a ⧸ (divisionPrism D d a hd).ideal

/-- 概要：構成した商候補は整 perfectoid。
方針：完全 prism の商と perfectoid 環の対応を使う。
規約：平坦性は未証明である。
使われ方：BS Thm 7.14（著者版 p.61）の別経路の構成部分。 -/
theorem divisionPerfectoidCandidate_isIntegralPerfectoid (hd : D.IsDistinguished d) :
    letI := divisionPrismCommRing D d a
    IsIntegralPerfectoid (DivisionPerfectoidCandidate D d a hd) p := by
  let := divisionPrismCommRing D d a
  exact (divisionPrism D d a hd).quotient_isIntegralPerfectoid
    (divisionPrism_isPerfect D d a hd)

/-- 概要：元の δ 環から perfectoid 候補への具体的な係数射。
方針：δ 除算完全化、実完備化、prism 商の射を合成する。
規約：忠実性を仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の関係式を商へ移す。 -/
def divisionPerfectoidCandidateMap (hd : D.IsDistinguished d) :
    letI := divisionPrismCommRing D d a
    A →+* DivisionPerfectoidCandidate D d a hd := by
  let := divisionPrismCommRing D d a
  exact (Ideal.Quotient.mk (divisionPrism D d a hd).ideal).comp
    ((pdCompletionUnit C p (j d)).comp j)

/-- 概要：候補への係数射は d を零へ送る。
方針：d の完備化像が prism の選択生成元であることを使う。
規約：任意関係族を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の基底商からの射を作る。 -/
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
使われ方：BS Rem 7.15（著者版 p.62）の多項式の根方程式を保持する。 -/
theorem divisionPerfectoidCandidateMap_relation (hd : D.IsDistinguished d) (s : σ) :
    letI := divisionPrismCommRing D d a
    divisionPerfectoidCandidateMap D d a hd (a s) = 0 := by
  let := divisionPrismCommRing D d a
  let q := (Ideal.Quotient.mk (divisionPrism D d a hd).ideal).comp
    (pdCompletionUnit C p (j d))
  obtain ⟨z, hz⟩ := pCompletedDeltaDivisionMap_dvd D d a s
  change q (j (a s)) = 0
  rw [hz, map_mul]
  have hqd : q (j d) = 0 := divisionPerfectoidCandidateMap_d D d a hd
  rw [hqd, zero_mul]

/-- 概要：元の d 商から perfectoid 候補への基底射。
方針：d が零に写ることを用いて商に降下する。
規約：基底射の忠実平坦性は主張しない。
使われ方：BS Thm 7.14（著者版 p.61）の候補を元の perfectoid 環の上に置く。 -/
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
