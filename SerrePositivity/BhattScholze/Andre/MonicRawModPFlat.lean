module

public import SerrePositivity.BhattScholze.Andre.MonicFrobeniusCoefficient
public import SerrePositivity.BhattScholze.DeltaAdjoinDivisionResidueRegular

/-!
# André E1・E2：モニック族の raw φ/p 包の実 mod p 商の忠実平坦性

## 概要

正次数モニック族の raw 同時 φ/p 包の実 p 商は、元の係数環 A/p 上忠実平坦。
BS 著者版 Cor 2.39（p.25）、Rem 7.15(1)（p.62）の実剰余計算に対応する。

## 方針

一般 δ 除算の raw 剰余の、初期係数商上の忠実平坦性を再利用する。
前工程の初期係数商の A/p 忠実平坦性と合成し、raw (p,p) 剰余を実 p 商と同定する。

## 規約

このファイルでは係数環の p 正則性、相対自由源の ghost 単射と単元 δ(p) を明示する。
次工程でこれらを証明から供給する。完備化後の平坦性は別工程。

## 使われ方

実剰余テンソルの忠実平坦性と p 完全忠実平坦性の判定に使う。
-/

@[expose] public noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (f : σ → Polynomial A)
variable (hpA : Function.Injective (fun x : A => (p : A) * x))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := MvPolynomial σ A) σ) →
    ℕ → RelativeFreeDeltaRing (R := MvPolynomial σ A) σ))
variable (w : Aˣ) (hw : (w : A) = D.delta (p : A))
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "a" => (fun s : σ => DeltaStructure.frobeniusLift E (monicRelation (f s) s))
local notation "Q" => MonicFrobeniusCoefficientQuotient D f
local notation "Res" => DeltaAdjoinDivisionResidue E (p : P) a
local notation "B" => DeltaAdjoinDivision E (p : P) a
local notation "QA" => A ⧸ Ideal.span {(p : A)}
local notation "wp" => Units.map (RingHom.toMonoidHom (MvPolynomial.C : A →+* P)) w

/-- 概要：raw (p,p) 剰余への元の A/p からの実係数射。
方針：初期係数商の標準係数射と一般 raw 剰余の係数射を合成する。
規約：源の p 正則性と ghost 単射を明示して一般定理を使用する。
使われ方：BS Cor 2.39（著者版 p.25）の実係数作用を固定する。 -/
def monicRawResidueBaseMap : QA →+* Res := by
  have hP : IsSMulRegular P (p : P) := by
    simpa only [map_natCast] using (show IsSMulRegular A (p : A) from hpA).of_flat (S := P)
  have hpP : Function.Injective (fun x : P => (p : P) * x) := hP
  let L := RelativeFreeDeltaRing (R := P) σ
  have hL : IsSMulRegular L (p : L) := by
    simpa only [map_natCast] using hP.of_flat (S := L)
  have hpL : Function.Injective (fun x : L => (p : L) * x) := hL
  have hwp : (wp : P) = DeltaStructure.delta E (p : P) := by
    change MvPolynomial.C (w : A) = _
    rw [hw, ← polynomialRankOneDeltaStructure_delta_C σ D (p : A), map_natCast]
  exact (deltaAdjoinDivisionResidueBaseMap E hpP hpL hg (p : P) a wp hwp).comp
    (monicFrobeniusCoefficientBaseMap D f)

/-- 概要：raw 剰余の A/p 係数射は元の A の係数の標準剰余像に一致する。
方針：二つの係数射の代表元公式を合成する。
規約：任意の元の A 係数について述べる。
使われ方：BS Rem 7.15（著者版 p.62）の元の係数射を保つ。 -/
theorem monicRawResidueBaseMap_mk (x : A) :
    monicRawResidueBaseMap D f hpA hg w hw (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (deltaAdjoinDivisionMap E (p : P) a (MvPolynomial.C x)) := by
  rw [monicRawResidueBaseMap, RingHom.comp_apply, monicFrobeniusCoefficientBaseMap_mk,
    deltaAdjoinDivisionResidueBaseMap_mk]

/-- 概要：raw 剰余の標準 A/p 代数構造。
方針：明示した係数射の toAlgebra を取る。
規約：利用時に局所導入する。
使われ方：BS Cor 2.39（著者版 p.25）の raw 剰余の平坦性。 -/
@[instance_reducible] def monicRawResidueBaseAlgebra : Algebra QA Res :=
  (monicRawResidueBaseMap D f hpA hg w hw).toAlgebra

/-- 概要：正次数モニック族の raw (p,p) 剰余は元の A/p 上忠実平坦。
方針：初期係数商と raw 剰余の二つの忠実平坦性を標準係数射で合成する。
規約：族の有限性は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実剰余の忠実平坦性。 -/
theorem monicRawResidue_faithfullyFlat
    (hf : ∀ s, (f s).Monic) (hdeg : ∀ s, 0 < (f s).natDegree) :
    letI := monicRawResidueBaseAlgebra D f hpA hg w hw
    Module.FaithfullyFlat QA Res := by
  have hP : IsSMulRegular P (p : P) := by
    simpa only [map_natCast] using (show IsSMulRegular A (p : A) from hpA).of_flat (S := P)
  have hpP : Function.Injective (fun x : P => (p : P) * x) := hP
  let L := RelativeFreeDeltaRing (R := P) σ
  have hL : IsSMulRegular L (p : L) := by
    simpa only [map_natCast] using hP.of_flat (S := L)
  have hpL : Function.Injective (fun x : L => (p : L) * x) := hL
  have hwp : (wp : P) = DeltaStructure.delta E (p : P) := by
    change MvPolynomial.C (w : A) = _
    rw [hw, ← polynomialRankOneDeltaStructure_delta_C σ D (p : A), map_natCast]
  let := monicFrobeniusCoefficientBaseAlgebra D f
  let := deltaAdjoinDivisionResidueBaseAlgebra E hpP hpL hg (p : P) a wp hwp
  let := monicRawResidueBaseAlgebra D f hpA hg w hw
  let : IsScalarTower QA Q Res := IsScalarTower.of_algebraMap_eq' rfl
  let := monicFrobeniusCoefficient_faithfullyFlat D f hf hdeg
  let := deltaAdjoinDivisionResidue_moduleFaithfullyFlat E hpP hpL hg (p : P) a wp hwp
  exact Module.FaithfullyFlat.trans QA Q Res

/-- 概要：実 raw p 商への元の A/p 係数射。
方針：raw (p,p) 剰余と実 p 商の既存同型の逆を合成する。
規約：同じ係数作用を実 p 商上に置く。
使われ方：BS Cor 2.39（著者版 p.25）の実 mod p 加群。 -/
def monicRawModPBaseMap : QA →+* (B ⧸ Ideal.span {(p : B)}) :=
  (deltaAdjoinDivisionPQuotientResidueEquiv E a).symm.toRingHom.comp
    (monicRawResidueBaseMap D f hpA hg w hw)

/-- 概要：実 p 商への係数射は標準 raw 係数射の剰余と一致する。
方針：剰余同型を適用して前の代表元公式に帰着する。
規約：元の A からの標準係数像を追跡する。
使われ方：BS Rem 7.15（著者版 p.62）の剰余テンソルとの比較。 -/
theorem monicRawModPBaseMap_mk (x : A) :
    monicRawModPBaseMap D f hpA hg w hw (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (deltaAdjoinDivisionMap E (p : P) a (MvPolynomial.C x)) := by
  rw [monicRawModPBaseMap, RingHom.comp_apply]
  apply (deltaAdjoinDivisionPQuotientResidueEquiv E a).injective
  change (deltaAdjoinDivisionPQuotientResidueEquiv E a)
    ((deltaAdjoinDivisionPQuotientResidueEquiv E a).symm _) = _
  rw [RingEquiv.apply_symm_apply, monicRawResidueBaseMap_mk,
    deltaAdjoinDivisionPQuotientResidueEquiv_mk]

/-- 概要：実 raw p 商の標準 A/p 代数構造。
方針：実 p 商への標準係数射の toAlgebra を使う。
規約：元の A/p の作用を変えない。
使われ方：BS Cor 2.39（著者版 p.25）の実 mod p 忠実平坦性。 -/
@[instance_reducible] def monicRawModPBaseAlgebra :
    Algebra QA (B ⧸ Ideal.span {(p : B)}) :=
  (monicRawModPBaseMap D f hpA hg w hw).toAlgebra

/-- 概要：raw (p,p) 剰余との比較は標準 A/p 作用を保つ代数同型。
方針：逆射で定義した係数射の可換性を確認する。
規約：通常の環同型だけでなく A/p 線形性を保持する。
使われ方：BS Rem 7.15（著者版 p.62）の忠実平坦性を実 p 商へ移す。 -/
def monicRawModPResidueAlgEquiv :
    letI := monicRawModPBaseAlgebra D f hpA hg w hw
    letI := monicRawResidueBaseAlgebra D f hpA hg w hw
    (B ⧸ Ideal.span {(p : B)}) ≃ₐ[QA] Res := by
  let := monicRawModPBaseAlgebra D f hpA hg w hw
  let := monicRawResidueBaseAlgebra D f hpA hg w hw
  apply AlgEquiv.ofRingEquiv (f := deltaAdjoinDivisionPQuotientResidueEquiv E a)
  intro x
  change (deltaAdjoinDivisionPQuotientResidueEquiv E a)
    (monicRawModPBaseMap D f hpA hg w hw x) = monicRawResidueBaseMap D f hpA hg w hw x
  rw [monicRawModPBaseMap, RingHom.comp_apply]
  exact (deltaAdjoinDivisionPQuotientResidueEquiv E a).apply_symm_apply _

/-- 概要：任意の正次数モニック族の raw φ/p 包の実 p 商は A/p 上忠実平坦。
方針：raw 剰余との代数同型で証明済みの剰余忠実平坦性を移す。
規約：係数射と族の正次数を明示し、完備化はまだ行わない。
使われ方：BS Rem 7.15(1)（著者版 p.62）の p 完全忠実平坦性の剰余入力。 -/
theorem monicRawModP_faithfullyFlat
    (hf : ∀ s, (f s).Monic) (hdeg : ∀ s, 0 < (f s).natDegree) :
    letI := monicRawModPBaseAlgebra D f hpA hg w hw
    Module.FaithfullyFlat QA (B ⧸ Ideal.span {(p : B)}) := by
  let := monicRawModPBaseAlgebra D f hpA hg w hw
  let := monicRawResidueBaseAlgebra D f hpA hg w hw
  let := monicRawResidue_faithfullyFlat D f hpA hg w hw hf hdeg
  exact Module.FaithfullyFlat.of_linearEquiv QA Res
    (monicRawModPResidueAlgEquiv D f hpA hg w hw).toLinearEquiv

end SerrePositivity.BhattScholze.Andre
