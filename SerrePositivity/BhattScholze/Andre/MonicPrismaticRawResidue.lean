module

public import SerrePositivity.BhattScholze.Andre.MonicPrismaticCoefficient
public import SerrePositivity.BhattScholze.Andre.RootedExtension.Division.DeltaAdjoinDivisionResidueRegular
public import SerrePositivity.BhattScholze.Andre.RootedExtension.DeltaRoot.DeltaRootSourceRegularGhost

/-!
# André E1・E2：一般 f/d 包の raw (p,d) 剰余の忠実平坦性

## 概要

p 正則な δ 係数環上で δ(d) が単元なら、任意正次数モニック族の raw f/d 包の
実 (p,d) 商は元の A/(p,d) 上忠実平坦。BS Rem 7.15（著者版 p.62）の剰余計算。

## 方針

初期係数商の通常モニック表示と、既存の一般 δ 除算包の実剰余表示を合成する。
原典の Prop 7.11 を使う経路とは異なる、明示的な係数射を保つ計算。

## 規約

raw 剰余自体の通常忠実平坦性である。導来還元の離散性や完備化後の平坦性は別工程。

## 使われ方

一般 f/d 包の実導来 (p,d) 還元との比較後に、忠実平坦性の入力となる。
-/

@[expose] public noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
variable (hpA : Function.Injective (fun x : A => (p : A) * x))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := MvPolynomial σ A) σ) →
    ℕ → RelativeFreeDeltaRing (R := MvPolynomial σ A) σ))
variable (w : Aˣ) (hw : (w : A) = D.delta d)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "a" => (fun s : σ => monicRelation (f s) s)
local notation "Q" => MonicPrismaticCoefficientQuotient p d f
local notation "Res" => DeltaAdjoinDivisionResidue E (MvPolynomial.C d) a
local notation "B" => DeltaAdjoinDivision E (MvPolynomial.C d) a
local notation "QA" => A ⧸ Ideal.span {(p : A), d}
local notation "wp" => Units.map (RingHom.toMonoidHom (MvPolynomial.C : A →+* P)) w

/-- 概要：一般 f/d 包の raw (p,d) 剰余への元の A/(p,d) からの実係数射。
方針：初期係数商の標準係数射と一般 raw 剰余の係数射を合成する。
規約：源の p 正則性と ghost 単射を明示して一般定理を使用する。
使われ方：BS Rem 7.15（著者版 p.62）の実係数作用を固定する。 -/
def monicPrismaticRawResidueBaseMap : QA →+* Res := by
  have hP : IsSMulRegular P (p : P) := by
    simpa only [map_natCast] using (show IsSMulRegular A (p : A) from hpA).of_flat (S := P)
  have hpP : Function.Injective (fun x : P => (p : P) * x) := hP
  let L := RelativeFreeDeltaRing (R := P) σ
  have hL : IsSMulRegular L (p : L) := by
    simpa only [map_natCast] using hP.of_flat (S := L)
  have hpL : Function.Injective (fun x : L => (p : L) * x) := hL
  have hwp : (wp : P) = DeltaStructure.delta E (MvPolynomial.C d) := by
    change MvPolynomial.C (w : A) = _
    rw [polynomialRankOneDeltaStructure_delta_C, hw]
  exact (deltaAdjoinDivisionResidueBaseMap E hpP hpL hg (MvPolynomial.C d) a wp hwp).comp
    (monicPrismaticCoefficientBaseMap p d f)

/-- 概要：raw 剰余の A/(p,d) 係数射は元の A の係数の標準剰余像に一致する。
方針：二つの係数射の代表元公式を合成する。
規約：任意の元の A 係数について述べる。
使われ方：BS Rem 7.15（著者版 p.62）の元の係数射を保つ。 -/
theorem monicPrismaticRawResidueBaseMap_mk (x : A) :
    monicPrismaticRawResidueBaseMap D d f hpA hg w hw (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (deltaAdjoinDivisionMap E (MvPolynomial.C d) a (MvPolynomial.C x)) := by
  rw [monicPrismaticRawResidueBaseMap, RingHom.comp_apply, monicPrismaticCoefficientBaseMap_mk,
    deltaAdjoinDivisionResidueBaseMap_mk]

/-- 概要：raw 剰余の標準 A/(p,d) 代数構造。
方針：明示した係数射の toAlgebra を取る。
規約：利用時に局所導入する。
使われ方：BS Rem 7.15（著者版 p.62）の raw 剰余の平坦性。 -/
@[instance_reducible] def monicPrismaticRawResidueBaseAlgebra : Algebra QA Res :=
  (monicPrismaticRawResidueBaseMap D d f hpA hg w hw).toAlgebra

/-- 概要：正次数モニック族の 一般 f/d 包の raw (p,d) 剰余は元の A/(p,d) 上忠実平坦。
方針：初期係数商と raw 剰余の二つの忠実平坦性を標準係数射で合成する。
規約：族の有限性は不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の実剰余の忠実平坦性。 -/
theorem monicPrismaticRawResidue_faithfullyFlat
    (hf : ∀ s, (f s).Monic) (hdeg : ∀ s, 0 < (f s).natDegree) :
    letI := monicPrismaticRawResidueBaseAlgebra D d f hpA hg w hw
    Module.FaithfullyFlat QA Res := by
  have hP : IsSMulRegular P (p : P) := by
    simpa only [map_natCast] using (show IsSMulRegular A (p : A) from hpA).of_flat (S := P)
  have hpP : Function.Injective (fun x : P => (p : P) * x) := hP
  let L := RelativeFreeDeltaRing (R := P) σ
  have hL : IsSMulRegular L (p : L) := by
    simpa only [map_natCast] using hP.of_flat (S := L)
  have hpL : Function.Injective (fun x : L => (p : L) * x) := hL
  have hwp : (wp : P) = DeltaStructure.delta E (MvPolynomial.C d) := by
    change MvPolynomial.C (w : A) = _
    rw [polynomialRankOneDeltaStructure_delta_C, hw]
  let := monicPrismaticCoefficientBaseAlgebra p d f
  let := deltaAdjoinDivisionResidueBaseAlgebra E hpP hpL hg (MvPolynomial.C d) a wp hwp
  let := monicPrismaticRawResidueBaseAlgebra D d f hpA hg w hw
  let : IsScalarTower QA Q Res := IsScalarTower.of_algebraMap_eq' rfl
  let := monicPrismaticCoefficient_faithfullyFlat p d f hf hdeg
  let := deltaAdjoinDivisionResidue_moduleFaithfullyFlat E hpP hpL hg (MvPolynomial.C d) a wp hwp
  exact Module.FaithfullyFlat.trans QA Q Res


/-- 概要：一般 f/d 包の raw 剰余に、distinguished 性だけから標準係数代数作用を定める。
方針：δ(d) の単元と、p 正則性から既存 ghost 単射を内部で供給する。
規約：外部 ghost 仮定を要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の実剰余の元の A/(p,d) 作用。 -/
@[instance_reducible] def monicPrismaticRawResidueAlgebraOfDistinguished
    (hdp : D.IsDistinguished d) : Algebra QA Res :=
  monicPrismaticRawResidueBaseAlgebra D d f hpA
    (deltaRootSource_ghostMap_injective (σ := σ) hpA) hdp.unit hdp.unit_spec

/-- 概要：任意正次数モニック族の一般 raw f/d 包の実 (p,d) 商は A/(p,d) 上忠実平坦。
方針：p 正則性から ghost 単射を供給し、初期係数商と実剰余の忠実平坦性を合成する。
規約：distinguished 性と p 正則性以外の δ 仮定は不要。族の有限性も要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の実導来還元との比較への剰余入力。 -/
theorem monicPrismaticRawResidue_faithfullyFlat_of_distinguished
    (hdp : D.IsDistinguished d) (hf : ∀ s, (f s).Monic)
    (hdeg : ∀ s, 0 < (f s).natDegree) :
    letI := monicPrismaticRawResidueAlgebraOfDistinguished D d f hpA hdp
    Module.FaithfullyFlat QA Res :=
  monicPrismaticRawResidue_faithfullyFlat D d f hpA
    (deltaRootSource_ghostMap_injective (σ := σ) hpA) hdp.unit hdp.unit_spec hf hdeg

end SerrePositivity.BhattScholze.Andre
