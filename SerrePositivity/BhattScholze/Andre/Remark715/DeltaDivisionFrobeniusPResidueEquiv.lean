module

public import SerrePositivity.BhattScholze.Andre.Remark715.DeltaDivisionPairResidueWitt
public import SerrePositivity.BhattScholze.Andre.Remark715.DistinguishedWittDenominatorNaturality

/-!
# André E1・E2：Frobenius 分母の raw 剰余と p 除算剰余

## 概要

distinguished d に対し A{b/φ(d)}/(p,d) と A{b/p}/(p,d) は A 係数を保って環同型。
BS Rem 7.15（著者版 p.62）の具体的 pd 包比較のための分母変換。

## 方針

各剰余の標準 Witt 点を分母正規化単元とその逆元で変換する。
通常 Witt 普遍性で環射を作り、係数と全 Witt 点で両逆合成を確認する。

## 規約

源の p 正則性と ghost 単射性を明示し、分子族 b の形は限定しない。
原典とは異なる通常 Witt 解による証明である。

## 使われ方

実完備化から得た Frobenius 側 raw 剰余を、既存の pd 表示に接続する。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (hpA : Function.Injective (fun x : A => (p : A) * x))
variable (hgA : Function.Injective (WittVector.ghostMap : WittVector p A → ℕ → A))
variable (hgL : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := A) σ) → ℕ → RelativeFreeDeltaRing (R := A) σ))
variable (d : A) (hd : D.IsDistinguished d) (b : σ → A)
local notation "Qφ" => DeltaDivisionPairResidue D (D.frobeniusLift d) b d
local notation "Qp" => DeltaDivisionPairResidue D (p : A) b d
local notation "qφ" => deltaDivisionPairResidueBase D (D.frobeniusLift d) b d
local notation "qp" => deltaDivisionPairResidueBase D (p : A) b d
local notation "wφ" => deltaDivisionPairResiduePoint D (D.frobeniusLift d) b d
local notation "wp" => deltaDivisionPairResiduePoint D (p : A) b d
local notation "hpφ" => deltaDivisionPairResidue_prime_zero D (D.frobeniusLift d) b d
local notation "hpp" => deltaDivisionPairResidue_prime_zero D (p : A) b d
local notation "vφ" => distinguishedWittResidueUnit D hpA qφ d hd hpφ
local notation "vp" => distinguishedWittResidueUnit D hpA qp d hd hpp

include hgA in
/-- 概要：通常係数射で自然数 p の全 Witt 像は Witt 環の p。
方針：Witt 環射の自然数保存を使う。
規約：元の通常係数射を保つ。
使われ方：BS Rem 7.15（著者版 p.62）の raw 剰余比較。 -/
theorem deltaWitt_prime_image {B : Type u} [CommRing B] (q : A →+* B) :
    WittVector.map q (deltaWittGhostVector D (p : A)) = (p : WittVector p B) := by
  change WittVector.map q (deltaWittGhostRingHom D hgA (p : A)) = _
  rw [map_natCast, map_natCast]

include hpA hgA hgL in
/-- 概要：p 分母の二元剰余の Witt 点は p 除算方程式を満たす。
方針：標準 raw 方程式の分母像を p と計算する。
規約：元の通常係数射を保つ。
使われ方：BS Rem 7.15（著者版 p.62）の raw 剰余比較。 -/
theorem deltaDivisionPResiduePoint_relation (s : σ) :
    (p : WittVector p Qp) * wp s = WittVector.map qp (deltaWittGhostVector D (b s)) := by
  have h := deltaDivisionPairResiduePoint_relation D (p : A) b d hpA hgL s
  rw [deltaWitt_prime_image D hgA] at h
  exact h

include hgA hgL in
/-- 概要：p 側の Witt 点を単元の逆元で変換すると Frobenius 分母の解になる。
方針：Frobenius 分母の p 単元倍表示を使う。
規約：元の通常係数射を保つ。
使われ方：BS Rem 7.15（著者版 p.62）の raw 剰余比較。 -/
theorem deltaDivisionFrobeniusToPResiduePoint_relation (s : σ) :
    WittVector.map qp (deltaWittGhostVector D (D.frobeniusLift d)) *
        ((↑(vp⁻¹) : WittVector p Qp) * wp s) =
      WittVector.map qp (deltaWittGhostVector D (b s)) := by
  rw [← distinguishedWittResidueUnit_mul D hpA qp d hd hpp hgA
    (deltaDivisionPairResidueBase_d D (p : A) b d)]
  rw [mul_assoc, ← mul_assoc (vp : WittVector p Qp) (↑(vp⁻¹) : WittVector p Qp)
    (wp s), Units.mul_inv, one_mul]
  exact deltaDivisionPResiduePoint_relation D hpA hgA hgL d b s

include hgA hgL in
/-- 概要：Frobenius 側の Witt 点を単元倍すると p 分母の解になる。
方針：分母の単元倍公式と元の方程式を使う。
規約：元の通常係数射を保つ。
使われ方：BS Rem 7.15（著者版 p.62）の raw 剰余比較。 -/
theorem deltaDivisionPToFrobeniusResiduePoint_relation (s : σ) :
    WittVector.map qφ (deltaWittGhostVector D (p : A)) *
        ((vφ : WittVector p Qφ) * wφ s) =
      WittVector.map qφ (deltaWittGhostVector D (b s)) := by
  rw [deltaWitt_prime_image D hgA, ← mul_assoc,
    distinguishedWittResidueUnit_mul D hpA qφ d hd hpφ hgA
      (deltaDivisionPairResidueBase_d D (D.frobeniusLift d) b d)]
  exact deltaDivisionPairResiduePoint_relation D (D.frobeniusLift d) b d hpA hgL s

/-- 概要：Frobenius 分母の二元剰余から p 分母の二元剰余への通常環射。
方針：p 側の Witt 点を正規化単元の逆元で変換する。
規約：元の係数射を保つ。
使われ方：BS Rem 7.15（著者版 p.62）の raw 剰余比較の順射。 -/
def deltaDivisionFrobeniusToPResidueMap : Qφ →+* Qp := by
  exact deltaDivisionPairResidueLift D (D.frobeniusLift d) b d hpA hgL qp
    (fun s => (↑(vp⁻¹) : WittVector p Qp) * wp s) hpp
    (deltaDivisionPairResidueBase_d D (p : A) b d)
    (deltaDivisionFrobeniusToPResiduePoint_relation D hpA hgA hgL d hd b)

/-- 概要：p 分母の二元剰余から Frobenius 分母の二元剰余への通常環射。
方針：Frobenius 側の Witt 点を正規化単元で変換する。
規約：元の係数射を保つ。
使われ方：BS Rem 7.15（著者版 p.62）の raw 剰余比較の逆射。 -/
def deltaDivisionPToFrobeniusResidueMap : Qp →+* Qφ := by
  exact deltaDivisionPairResidueLift D (p : A) b d hpA hgL qφ
    (fun s => (vφ : WittVector p Qφ) * wφ s) hpφ
    (deltaDivisionPairResidueBase_d D (D.frobeniusLift d) b d)
    (deltaDivisionPToFrobeniusResiduePoint_relation D hpA hgA hgL d hd b)

local notation "F" => deltaDivisionFrobeniusToPResidueMap D hpA hgA hgL d hd b
local notation "G" => deltaDivisionPToFrobeniusResidueMap D hpA hgA hgL d hd b

/-- 概要：順比較射は元の全係数を保つ。
方針：二元商への Witt 評価の係数公式を使う。
規約：全ての r∈A に対して述べる。
使われ方：BS Rem 7.15（著者版 p.62）の係数作用の確認。 -/
theorem deltaDivisionFrobeniusToPResidueMap_base (r : A) : F (qφ r) = qp r :=
  deltaDivisionPairResidueLift_base _ _ _ _ _ _ _ _ _ _ _ _

/-- 概要：逆比較射も元の全係数を保つ。
方針：二元商への Witt 評価の係数公式を使う。
規約：全ての r∈A に対して述べる。
使われ方：BS Rem 7.15（著者版 p.62）の逆比較の係数作用。 -/
theorem deltaDivisionPToFrobeniusResidueMap_base (r : A) : G (qp r) = qφ r :=
  deltaDivisionPairResidueLift_base _ _ _ _ _ _ _ _ _ _ _ _

/-- 概要：順比較射は全 Witt 点を正規化単元の逆元倍へ送る。
方針：二元商への Witt 評価の点公式を使う。
規約：全 Witt 係数を同時に追う。
使われ方：BS Rem 7.15（著者版 p.62）の逆合成の計算。 -/
theorem deltaDivisionFrobeniusToPResidueMap_point (s : σ) :
    WittVector.map F (wφ s) = (↑(vp⁻¹) : WittVector p Qp) * wp s :=
  deltaDivisionPairResidueLift_point _ _ _ _ _ _ _ _ _ _ _ _

/-- 概要：逆比較射は全 Witt 点を正規化単元倍へ送る。
方針：二元商への Witt 評価の点公式を使う。
規約：全 Witt 係数を同時に追う。
使われ方：BS Rem 7.15（著者版 p.62）のもう一方の逆合成の計算。 -/
theorem deltaDivisionPToFrobeniusResidueMap_point (s : σ) :
    WittVector.map G (wp s) = (vφ : WittVector p Qφ) * wφ s :=
  deltaDivisionPairResidueLift_point _ _ _ _ _ _ _ _ _ _ _ _

/-- 概要：順射と元の係数射の合成は p 側の係数射。
方針：全係数上の公式で外延性を使う。
規約：元の通常係数射を保つ。
使われ方：BS Rem 7.15（著者版 p.62）の raw 剰余比較。 -/
theorem deltaDivisionFrobeniusToPResidueMap_comp_base : (F).comp qφ = qp := by
  ext r
  exact deltaDivisionFrobeniusToPResidueMap_base D hpA hgA hgL d hd b r

/-- 概要：逆射と元の係数射の合成は Frobenius 側の係数射。
方針：全係数上の公式で外延性を使う。
規約：元の通常係数射を保つ。
使われ方：BS Rem 7.15（著者版 p.62）の raw 剰余比較。 -/
theorem deltaDivisionPToFrobeniusResidueMap_comp_base : (G).comp qp = qφ := by
  ext r
  exact deltaDivisionPToFrobeniusResidueMap_base D hpA hgA hgL d hd b r

/-- 概要：逆射の後に順射を適用する合成は p 側の恒等射。
方針：係数と全 Witt 点で単元の自然性と逆元による相殺を使う。
規約：零環の場合も含める。
使われ方：BS Rem 7.15（著者版 p.62）の raw 剰余同型の片側逆。 -/
theorem deltaDivisionFrobeniusPResidue_comp : (F).comp G = RingHom.id Qp := by
  apply deltaDivisionPairResidueRingHom_ext D (p : A) b d hpA
  · intro r
    change F (G (qp r)) = qp r
    rw [deltaDivisionPToFrobeniusResidueMap_base, deltaDivisionFrobeniusToPResidueMap_base]
  · intro s
    rw [← witt_map_comp_apply, deltaDivisionPToFrobeniusResidueMap_point, map_mul,
      distinguishedWittResidueUnit_map D hpA qφ d hd hpφ qp hpp F
        (deltaDivisionFrobeniusToPResidueMap_comp_base D hpA hgA hgL d hd b),
      deltaDivisionFrobeniusToPResidueMap_point]
    change (vp : WittVector p Qp) * ((↑(vp⁻¹) : WittVector p Qp) * wp s) = wp s
    rw [← mul_assoc, Units.mul_inv, one_mul]

/-- 概要：順射の後に逆射を適用する合成は Frobenius 側の恒等射。
方針：全 Witt 点で逆単元の自然性と相殺を使う。
規約：通常環射の外延性に帰着する。
使われ方：BS Rem 7.15（著者版 p.62）の raw 剰余同型のもう片側逆。 -/
theorem deltaDivisionPFrobeniusResidue_comp : (G).comp F = RingHom.id Qφ := by
  apply deltaDivisionPairResidueRingHom_ext D (D.frobeniusLift d) b d hpA
  · intro r
    change G (F (qφ r)) = qφ r
    rw [deltaDivisionFrobeniusToPResidueMap_base, deltaDivisionPToFrobeniusResidueMap_base]
  · intro s
    rw [← witt_map_comp_apply, deltaDivisionFrobeniusToPResidueMap_point, map_mul,
      distinguishedWittResidueUnit_inv_map D hpA qp d hd hpp qφ hpφ G
        (deltaDivisionPToFrobeniusResidueMap_comp_base D hpA hgA hgL d hd b),
      deltaDivisionPToFrobeniusResidueMap_point]
    change (↑(vφ⁻¹) : WittVector p Qφ) * ((vφ : WittVector p Qφ) * wφ s) = wφ s
    rw [← mul_assoc, Units.inv_mul, one_mul]

/-- 概要：distinguished 元の Frobenius 分母の raw 剰余は p 分母の raw 剰余と環同型。
方針：Witt 単元変換で構成した二つの通常環射と両逆合成を束ねる。
規約：分子族の形・モニック性・有限性は仮定しない。
使われ方：BS Rem 7.15（著者版 p.62）の具体的 pd 表示への分母の接続。 -/
def deltaDivisionFrobeniusPResidueEquiv : Qφ ≃+* Qp :=
  RingEquiv.ofRingHom F G
    (deltaDivisionFrobeniusPResidue_comp D hpA hgA hgL d hd b)
    (deltaDivisionPFrobeniusResidue_comp D hpA hgA hgL d hd b)

/-- 概要：分母変換の環同型は元の全係数を保つ。
方針：順比較射の係数公式を使う。
規約：元の A 係数作用に関する同型。
使われ方：BS Rem 7.15（著者版 p.62）の pd 包比較へ係数を保って合成する。 -/
theorem deltaDivisionFrobeniusPResidueEquiv_base (r : A) :
    deltaDivisionFrobeniusPResidueEquiv D hpA hgA hgL d hd b (qφ r) = qp r :=
  deltaDivisionFrobeniusToPResidueMap_base D hpA hgA hgL d hd b r

end SerrePositivity.BhattScholze.Andre
