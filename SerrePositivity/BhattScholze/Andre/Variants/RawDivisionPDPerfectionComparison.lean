module

public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaPDCompletionPerfectionComparison
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaPerfectionPDCompletionComparison
public import SerrePositivity.BhattScholze.Andre.DivisionPerfectoidCandidate

/-!
# André E1・E2：任意 raw δ 割り算包の実完備化先行完全化と既存完全 prism 候補

## 概要

任意の分子族について、元の raw 包を実完備化してから δ 完全化し再び実完備化する手順は、
既存の完全 prism 候補と標準係数射・生成元を保って環同型。
分母が distinguished なら生成元商も同型で整 perfectoid。
BS Cor 7.3（著者版 p.56）、Rem 7.15（p.62）の構成比較。

## 方針

既存の実完備化・δ 完全化の順序交換同型と p 完備化先行比較を合成する。
B4-6 の根方程式に特化した比較を、方程式を使わない部分について一般化する。

## 規約

元の raw 包・実 H⁰ と標準射を使う。忠実平坦性の保存はこの比較だけから結論しない。

## 使われ方

無限根モニック実候補の完全 δ 化を、既存の perfectoid 候補へ接続する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open SerrePositivity.DerivedCompletion
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (a : σ → A)
local notation "Raw" => DeltaAdjoinDivision D d a
local notation "F" => deltaAdjoinDivisionStructure D d a
local notation "ι" => deltaAdjoinDivisionMap D d a
local notation "z" => ι d
local notation "S" => PDCompletionH0 Raw p z
local notation "G" => deltaPDCompletionStructure F z
local notation "v" => pdCompletionUnit Raw p z
local notation "C" => DeltaPerfection G
local notation "x" => deltaPerfectionOf G 0 (v z)
local notation "H" => PDCompletionH0 C p x
local notation "s" => pdCompletionUnit C p x
local notation "rH" => RingHom.comp (RingHom.comp s (deltaPerfectionOf G 0)) v
local notation "rV" => RingHom.comp
  (pdCompletionUnit (PCompletedDeltaPerfection F) p (pCompletedDeltaPerfectionMap F z))
  (pCompletedDeltaPerfectionMap F)

/-- 概要：任意 raw 包の実完備化先行完全化は既存の完全 prism 台環候補と環同型。
方針：二つの既存の順序比較を合成する。
規約：分子族・分母を任意とし、正則性を要求しない。
使われ方：BS Cor 7.3（著者版 p.56）、Rem 7.15（p.62）の一般比較。 -/
def rawDivisionPDPerfectionEquiv :
    let := pdCompletionCommRing Raw p z
    let := pdCompletionCommRing C p x
    let := divisionPrismCommRing D d a
    let := pdCompletionCommRing (PCompletedDeltaPerfection F) p (pCompletedDeltaPerfectionMap F z)
    H ≃+* DivisionPrismCarrier D d a := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing (DeltaPerfection F) p (deltaPerfectionOf F 0 z)
  let := pdCompletionCommRing C p x
  let := divisionPrismCommRing D d a
  let := pdCompletionCommRing (PCompletedDeltaPerfection F) p (pCompletedDeltaPerfectionMap F z)
  exact (deltaPDCompletionPerfectionEquiv F z).symm.trans (deltaPerfectionPDCompletionEquiv F z)

/-- 概要：一般比較は元の raw 包からの標準射を保つ。
方針：二つの既存比較の raw 係数公式を順に使う。
規約：全ての raw 代表元を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の係数作用の追跡。 -/
theorem rawDivisionPDPerfectionEquiv_comp_raw :
    let := pdCompletionCommRing Raw p z
    let := pdCompletionCommRing C p x
    let := divisionPrismCommRing D d a
    let := pdCompletionCommRing (PCompletedDeltaPerfection F) p (pCompletedDeltaPerfectionMap F z)
    (rawDivisionPDPerfectionEquiv D d a).toRingHom.comp rH = rV := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing (DeltaPerfection F) p (deltaPerfectionOf F 0 z)
  let := pdCompletionCommRing C p x
  let := divisionPrismCommRing D d a
  let := pdCompletionCommRing (PCompletedDeltaPerfection F) p (pCompletedDeltaPerfectionMap F z)
  apply RingHom.ext
  intro b
  have h : (deltaPDCompletionPerfectionEquiv F z).symm (rH b) =
      pdCompletionUnit (DeltaPerfection F) p (deltaPerfectionOf F 0 z)
        (deltaPerfectionOf F 0 b) :=
    RingHom.congr_fun (deltaPDCompletionPerfectionInverse_spec F z).2 b
  change deltaPerfectionPDCompletionEquiv F z
    ((deltaPDCompletionPerfectionEquiv F z).symm (rH b)) = rV b
  rw [h]
  exact RingHom.congr_fun (deltaPerfectionPDCompletionEquiv_spec F z).2.2 b

/-- 概要：一般比較の順逆両方向は指定 δ 構造を保つ。
方針：二つの順序比較の両方向の δ 性を合成する。
規約：完備化の既存 δ 構造を用いる。
使われ方：BS Cor 7.3（著者版 p.56）の完全 δ 化比較。 -/
theorem rawDivisionPDPerfectionEquiv_isDeltaHom :
    let := pdCompletionCommRing Raw p z
    let := pdCompletionCommRing C p x
    let := divisionPrismCommRing D d a
    let := pdCompletionCommRing (PCompletedDeltaPerfection F) p (pCompletedDeltaPerfectionMap F z)
    (deltaPDCompletionStructure (deltaPerfectionStructure G) x).IsDeltaHom
      (deltaPDCompletionStructure (pCompletedDeltaPerfectionStructure F)
        (pCompletedDeltaPerfectionMap F z)) (rawDivisionPDPerfectionEquiv D d a).toRingHom ∧
    (deltaPDCompletionStructure (pCompletedDeltaPerfectionStructure F)
        (pCompletedDeltaPerfectionMap F z)).IsDeltaHom
      (deltaPDCompletionStructure (deltaPerfectionStructure G) x)
      (rawDivisionPDPerfectionEquiv D d a).symm.toRingHom := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing (DeltaPerfection F) p (deltaPerfectionOf F 0 z)
  let := pdCompletionCommRing C p x
  let := divisionPrismCommRing D d a
  let := pdCompletionCommRing (PCompletedDeltaPerfection F) p (pCompletedDeltaPerfectionMap F z)
  exact ⟨(deltaPerfectionPDCompletionEquiv_spec F z).1.comp
      (deltaPDCompletionPerfectionEquiv_spec F z).2.1,
    (deltaPDCompletionPerfectionEquiv_spec F z).1.comp
      (deltaPerfectionPDCompletionEquiv_spec F z).2.1⟩

/-- 概要：一般比較は指定分母の両候補での標準像を保つ。
方針：raw 係数公式を分母像で評価する。
規約：生成元を変更しない。
使われ方：BS Rem 7.15（著者版 p.62）の商環比較。 -/
theorem rawDivisionPDPerfectionEquiv_generator :
    let := pdCompletionCommRing Raw p z
    let := pdCompletionCommRing C p x
    let := divisionPrismCommRing D d a
    let := pdCompletionCommRing (PCompletedDeltaPerfection F) p (pCompletedDeltaPerfectionMap F z)
    rawDivisionPDPerfectionEquiv D d a (s x) =
      pdCompletionUnit (PCompletedDeltaDivision D d a) p
        (pCompletedDeltaDivisionMap D d a d) (pCompletedDeltaDivisionMap D d a d) := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p x
  let := divisionPrismCommRing D d a
  let := pdCompletionCommRing (PCompletedDeltaPerfection F) p (pCompletedDeltaPerfectionMap F z)
  exact RingHom.congr_fun (rawDivisionPDPerfectionEquiv_comp_raw D d a) z

/-- 概要：指定生成元商は既存の整 perfectoid 候補と環同型。
方針：生成元保存を主イデアル商へ降ろす。
規約：分母の distinguished 性のみを追加する。
使われ方：BS Cor 7.3（著者版 p.56）、Rem 7.15（p.62）の perfectoid 商比較。 -/
def rawDivisionPDPerfectionQuotientEquiv (hd : D.IsDistinguished d) :
    let := pdCompletionCommRing Raw p z
    let := pdCompletionCommRing C p x
    let := divisionPrismCommRing D d a
    let := pdCompletionCommRing (PCompletedDeltaPerfection F) p (pCompletedDeltaPerfectionMap F z)
    (H ⧸ Ideal.span {s x}) ≃+* DivisionPerfectoidCandidate D d a hd := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p x
  let := divisionPrismCommRing D d a
  let := pdCompletionCommRing (PCompletedDeltaPerfection F) p (pCompletedDeltaPerfectionMap F z)
  exact Ideal.quotientEquiv _ _ (rawDivisionPDPerfectionEquiv D d a) (by
    rw [Ideal.map_span, Set.image_singleton]
    change Ideal.span {(divisionPrism D d a hd).generator} =
      Ideal.span {rawDivisionPDPerfectionEquiv D d a (s x)}
    rw [rawDivisionPDPerfectionEquiv_generator]
    rfl)

/-- 概要：商比較は代表元に一般環同型を適用する。
方針：主イデアル商への降下の定義を使う。
規約：実 H⁰ の任意の元を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の係数射と根の追跡。 -/
theorem rawDivisionPDPerfectionQuotientEquiv_mk (hd : D.IsDistinguished d) :
    let := pdCompletionCommRing Raw p z
    let := pdCompletionCommRing C p x
    let := divisionPrismCommRing D d a
    let := pdCompletionCommRing (PCompletedDeltaPerfection F) p (pCompletedDeltaPerfectionMap F z)
    ∀ b : H, rawDivisionPDPerfectionQuotientEquiv D d a hd (Ideal.Quotient.mk _ b) =
      Ideal.Quotient.mk _ (rawDivisionPDPerfectionEquiv D d a b) := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p x
  let := divisionPrismCommRing D d a
  let := pdCompletionCommRing (PCompletedDeltaPerfection F) p (pCompletedDeltaPerfectionMap F z)
  dsimp only
  intro b
  rfl

/-- 概要：生成元商の比較も元の基底環からの自然係数射を保つ。
方針：raw 係数公式を主イデアル商射で送る。
規約：全ての元の係数を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の自然な根付き候補の比較。 -/
theorem rawDivisionPDPerfectionQuotientEquiv_comp_coefficient (hd : D.IsDistinguished d) :
    let := pdCompletionCommRing Raw p z
    let := pdCompletionCommRing C p x
    let := divisionPrismCommRing D d a
    let := pdCompletionCommRing (PCompletedDeltaPerfection F) p (pCompletedDeltaPerfectionMap F z)
    (rawDivisionPDPerfectionQuotientEquiv D d a hd).toRingHom.comp
      ((Ideal.Quotient.mk (Ideal.span {s x})).comp ((rH).comp ι)) =
      divisionPerfectoidCandidateMap D d a hd := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p x
  let := divisionPrismCommRing D d a
  let := pdCompletionCommRing (PCompletedDeltaPerfection F) p (pCompletedDeltaPerfectionMap F z)
  apply RingHom.ext
  intro b
  change Ideal.Quotient.mk (divisionPrism D d a hd).ideal
    (rawDivisionPDPerfectionEquiv D d a (rH (ι b))) = _
  exact congrArg (Ideal.Quotient.mk (divisionPrism D d a hd).ideal)
    (RingHom.congr_fun (rawDivisionPDPerfectionEquiv_comp_raw D d a) (ι b))

/-- 概要：元の実完備化を δ 完全化し再完備化した標準生成元商は整 perfectoid。
方針：標準商環同型で既存の完全 prism 商の整 perfectoid 性を移す。
規約：忠実平坦性の保存を結論に含めない。
使われ方：BS Cor 7.3（著者版 p.56）、Rem 7.15（p.62）の最終環候補。 -/
theorem rawDivisionPDPerfectionQuotient_isIntegralPerfectoid (hd : D.IsDistinguished d) :
    let := pdCompletionCommRing Raw p z
    let := pdCompletionCommRing C p x
    IsIntegralPerfectoid (H ⧸ Ideal.span {s x}) p := by
  let := pdCompletionCommRing Raw p z
  let := pdCompletionCommRing C p x
  let := divisionPrismCommRing D d a
  let := pdCompletionCommRing (PCompletedDeltaPerfection F) p (pCompletedDeltaPerfectionMap F z)
  exact isIntegralPerfectoid_of_ringEquiv p (rawDivisionPDPerfectionQuotientEquiv D d a hd).symm
    (divisionPerfectoidCandidate_isIntegralPerfectoid D d a hd)

end SerrePositivity.BhattScholze.Andre
