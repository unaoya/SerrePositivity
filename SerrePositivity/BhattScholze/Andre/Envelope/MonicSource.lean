module

public import SerrePositivity.BhattScholze.Andre.OrdinaryRoots.Family
public import SerrePositivity.BhattScholze.Andre.Envelope.Normalized
public import SerrePositivity.BhattScholze.Andre.Envelope.DivisionResidue
public import SerrePositivity.BhattScholze.Andre.Envelope.RootSource
public import SerrePositivity.BhattScholze.Andre.Envelope.MonicCandidate
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.PrismaticResidue
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Koszul.Complete
public import SerrePositivity.HomologicalAlgebra.DerivedQuotientKoszul
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.Restriction.Completion
public import SerrePositivity.HomologicalAlgebra.DerivedRestrictionConservative
public import SerrePositivity.BhattScholze.Delta.Division.Source
public import SerrePositivity.HomologicalAlgebra.DerivedTensorH0Algebra
public import SerrePositivity.HomologicalAlgebra.DerivedTensorNonpositive
public import SerrePositivity.HomologicalAlgebra.DerivedCompletion.BoundedAboveCompletion
public import SerrePositivity.HomologicalAlgebra.AlgebraRestrictionSingle
public import SerrePositivity.HomologicalAlgebra.NilpotentDerivedReduction

/-!
# モニック源と raw 包の完備化比較

## 概要
一般の f/d 包の初期係数商と raw (p,d) 剰余の忠実平坦性、商還元の H⁰ の忠実平坦性、(p,d) 還元と raw 残余商、逐次完備化後の剰余、モニック f/d 源と raw 包の完備化比較（係数・非正性・H⁰・制限・PD）、源の逐次完備性と生成元冪商の完備性・標準冪零還元、G9 入力。
BS 著者版 Remark 7.15 のモニック根の包に使う、源の剰余の忠実平坦性と完備化の比較を与える。

## 方針
構成ごとに補題をまとめ、各節で共通の仮定を明示する。

## 規約
係数環・素数・正則性の仮定は各宣言で明示する。

## 使われ方
`Perfection/PerfectPrismMonic`、`PowerRootEnvelope/Unconditional/Source`、`Variants/ArbitraryFamily`、`Variants/MonicRootedExtension`。
-/

universe u

/-! ## 一般 f/d 包の初期係数商

## 概要

任意正次数モニック族の f/d 包の初期係数商は、元の A/(p,d) 上忠実平坦。
BS 著者版 Remark 7.15（著者版 p.62）の一般除算包の剰余計算の係数部分。

## 方針

実イデアルを (p,d) の係数拡張とモニック関係イデアルの和に分け、通常の全族商との
具体的同型で忠実平坦性を移す。原典の BS 著者版 Proposition 7.11 を使う経路とは異なる計算。

## 規約

δ 構造も係数環の正則性も不要。導来基底変更や完備化後の平坦性は主張しない。

## 使われ方

一般 f/d 包の raw (p,d) 剰余を元の係数環上へ戻す。
-/

@[expose] public noncomputable section MonicPrismaticCoefficient

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

variable {A σ : Type u} [CommRing A]
variable (p : ℕ) (d : A) (f : σ → Polynomial A)
local notation "P" => MvPolynomial σ A
local notation "r" => (fun s : σ => monicRelation (f s) s)
local notation "I" => Ideal.span {(p : A), d}
local notation "QA" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "J" => deltaDivisionFirstBaseIdeal (p := p) (MvPolynomial.C d) r
local notation "g" => (fun s : σ => Polynomial.map q (f s))
local notation "C" => PolynomialFamilyQuotient g

/-- 概要：モニック関係族の raw f/d 包の初期係数商。
方針：既存 δ 除算の初期係数イデアルの商をそのまま使う。
規約：関係式のモニック性は定義に含めない。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の実 mod (p,d) 表示の係数環。 -/
abbrev MonicPrismaticCoefficientQuotient := P ⧸ J

/-- 概要：初期係数イデアルは (p,d) の係数拡張と関係多項式のイデアルの和。
方針：係数イデアルの拡張とモニック関係イデアルの定義を展開する。
規約：任意多項式族に成立する。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の係数商を通常モニック商へ移す。 -/
theorem monicPrismaticCoefficientIdeal_eq :
    J = (I).map (MvPolynomial.C : A →+* P) ⊔ polynomialFamilyRelationIdeal f := by
  simp only [Ideal.map_span, Set.image_pair, map_natCast,
    deltaDivisionFirstBaseIdeal, polynomialFamilyRelationIdeal]

/-- 概要：f/d 包の初期係数商は mod (p,d) の多項式の通常商に同型。
方針：初期イデアルの表示と全族の係数商の交換同型を合成する。
規約：この同型は任意族に対して定義する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実剰余の通常忠実平坦性。 -/
def monicPrismaticCoefficientEquiv : MonicPrismaticCoefficientQuotient p d f ≃+* C :=
  (Ideal.quotEquivOfEq (monicPrismaticCoefficientIdeal_eq p d f)).trans
    (polynomialFamilyBaseQuotientEquiv I (f))

/-- 概要：係数商同型は多項式の係数を mod (p,d) に写す。
方針：商イデアル同定と係数商同型の代表元公式を使う。
規約：元の変数は保持する。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の実係数作用の比較。 -/
theorem monicPrismaticCoefficientEquiv_mk (x : P) :
    monicPrismaticCoefficientEquiv p d f (Ideal.Quotient.mk J x) =
      Ideal.Quotient.mk (polynomialFamilyRelationIdeal g) (MvPolynomial.map q x) := by
  rw [monicPrismaticCoefficientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    polynomialFamilyBaseQuotientEquiv_mk]

/-- 概要：表示同型は元の係数の標準像を A/(p,d) の通常係数作用に対応させる。
方針：代表元公式に定数多項式を代入する。
規約：元の A の任意元で述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の係数環への平坦性移送。 -/
theorem monicPrismaticCoefficientEquiv_C (x : A) :
    monicPrismaticCoefficientEquiv p d f (Ideal.Quotient.mk J (MvPolynomial.C x)) =
      algebraMap QA C (q x) := by
  rw [monicPrismaticCoefficientEquiv_mk, MvPolynomial.map_C]
  rfl

/-- 概要：初期係数商への標準 A/(p,d) 係数射。
方針：通常商への係数射を表示同型の逆で戻す。
規約：次の代表元公式で自然な係数射に一致することを確認する。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の実係数商の代数構造。 -/
def monicPrismaticCoefficientBaseMap : QA →+* MonicPrismaticCoefficientQuotient p d f :=
  (monicPrismaticCoefficientEquiv p d f).symm.toRingHom.comp (algebraMap QA C)

/-- 概要：標準 A/(p,d) 係数射は元の A 係数の自然な商像で与えられる。
方針：表示同型を適用して元の係数像を比較する。
規約：環射の定義だけでなく代表元での等式を保証する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 商の係数作用。 -/
theorem monicPrismaticCoefficientBaseMap_mk (x : A) :
    monicPrismaticCoefficientBaseMap p d f (q x) = Ideal.Quotient.mk J (MvPolynomial.C x) := by
  apply (monicPrismaticCoefficientEquiv p d f).injective
  change (monicPrismaticCoefficientEquiv p d f)
    ((monicPrismaticCoefficientEquiv p d f).symm _) = _
  rw [RingEquiv.apply_symm_apply, monicPrismaticCoefficientEquiv_C]

/-- 概要：標準係数射による初期係数商の A/(p,d) 代数構造。
方針：明示した環射の toAlgebra を用いる。
規約：利用箇所で局所的に導入する。
使われ方：BS 著者版 Corollary 2.39（著者版 p.25）の係数商の忠実平坦性。 -/
@[instance_reducible] def monicPrismaticCoefficientBaseAlgebra :
    Algebra QA (MonicPrismaticCoefficientQuotient p d f) :=
  (monicPrismaticCoefficientBaseMap p d f).toAlgebra

/-- 概要：初期係数商の表示は標準 A/(p,d) 係数作用に関する代数同型。
方針：表示同型の逆で定義した係数射との可換性を使う。
規約：元の A/(p,d) スカラーを変えない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の忠実平坦性の移送。 -/
def monicPrismaticCoefficientAlgEquiv :
    letI := monicPrismaticCoefficientBaseAlgebra p d f
    MonicPrismaticCoefficientQuotient p d f ≃ₐ[QA] C := by
  let := monicPrismaticCoefficientBaseAlgebra p d f
  apply AlgEquiv.ofRingEquiv (f := monicPrismaticCoefficientEquiv p d f)
  intro x
  exact (monicPrismaticCoefficientEquiv p d f).apply_symm_apply _

/-- 概要：正次数モニック族の f/d 包の初期係数商は A/(p,d) 上忠実平坦。
方針：mod (p,d) の非零係数環ではモニック性と次数を保つ係数変更を使い、
通常の任意モニック族商の忠実平坦性を移す。零係数商は加群の自明性で処理する。
規約：A の p 正則性も族の有限性も不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の raw 実 mod (p,d) 商の忠実平坦性の係数入力。 -/
theorem monicPrismaticCoefficient_faithfullyFlat
    (hf : ∀ s, (f s).Monic) (hdeg : ∀ s, 0 < (f s).natDegree) :
    letI := monicPrismaticCoefficientBaseAlgebra p d f
    Module.FaithfullyFlat QA (MonicPrismaticCoefficientQuotient p d f) := by
  let := monicPrismaticCoefficientBaseAlgebra p d f
  have hc : Module.FaithfullyFlat QA C := by
    rcases subsingleton_or_nontrivial QA with hs | hn
    · let := hs
      let : Subsingleton C := Module.subsingleton QA C
      rw [Module.FaithfullyFlat.iff_flat_and_rTensor_reflects_triviality]
      refine ⟨inferInstance, ?_⟩
      intro N _ _ _
      exact Module.subsingleton QA N
    · let := hn
      apply polynomialFamilyQuotient_faithfullyFlat g
      · intro s
        exact (hf s).map q
      · intro s
        rw [(hf s).natDegree_map]
        exact hdeg s
  let := hc
  exact Module.FaithfullyFlat.of_linearEquiv QA C
    (monicPrismaticCoefficientAlgEquiv p d f).toLinearEquiv

end SerrePositivity.BhattScholze.Andre

end MonicPrismaticCoefficient

/-! ## 一般 f/d 包の raw (p,d) 剰余の忠実平坦性

## 概要

p 正則な δ 係数環上で δ(d) が単元なら、任意正次数モニック族の raw f/d 包の
実 (p,d) 商は元の A/(p,d) 上忠実平坦。BS 著者版 Remark 7.15（著者版 p.62）の剰余計算。

## 方針

初期係数商の通常モニック表示と、既存の一般 δ 除算包の実剰余表示を合成する。
原典の BS 著者版 Proposition 7.11 を使う経路とは異なる、明示的な係数射を保つ計算。

## 規約

raw 剰余自体の通常忠実平坦性である。導来還元の離散性や完備化後の平坦性は別工程。

## 使われ方

一般 f/d 包の実導来 (p,d) 還元との比較後に、忠実平坦性の入力となる。
-/

@[expose] public noncomputable section MonicPrismaticRawResidue

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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実係数作用を固定する。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の係数射を保つ。 -/
theorem monicPrismaticRawResidueBaseMap_mk (x : A) :
    monicPrismaticRawResidueBaseMap D d f hpA hg w hw (Ideal.Quotient.mk _ x) =
      Ideal.Quotient.mk _ (deltaAdjoinDivisionMap E (MvPolynomial.C d) a (MvPolynomial.C x)) := by
  rw [monicPrismaticRawResidueBaseMap, RingHom.comp_apply, monicPrismaticCoefficientBaseMap_mk,
    deltaAdjoinDivisionResidueBaseMap_mk]

/-- 概要：raw 剰余の標準 A/(p,d) 代数構造。
方針：明示した係数射の toAlgebra を取る。
規約：利用時に局所導入する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 剰余の平坦性。 -/
@[instance_reducible] def monicPrismaticRawResidueBaseAlgebra : Algebra QA Res :=
  (monicPrismaticRawResidueBaseMap D d f hpA hg w hw).toAlgebra

/-- 概要：正次数モニック族の 一般 f/d 包の raw (p,d) 剰余は元の A/(p,d) 上忠実平坦。
方針：初期係数商と raw 剰余の二つの忠実平坦性を標準係数射で合成する。
規約：族の有限性は不要。
使われ方：BS 著者版 Remark 7.15(1)（著者版 p.62）の実剰余の忠実平坦性。 -/
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
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実剰余の元の A/(p,d) 作用。 -/
@[instance_reducible] def monicPrismaticRawResidueAlgebraOfDistinguished
    (hdp : D.IsDistinguished d) : Algebra QA Res :=
  monicPrismaticRawResidueBaseAlgebra D d f hpA
    (deltaRootSource_ghostMap_injective (σ := σ) hpA) hdp.unit hdp.unit_spec

/-- 概要：任意正次数モニック族の一般 raw f/d 包の実 (p,d) 商は A/(p,d) 上忠実平坦。
方針：p 正則性から ghost 単射を供給し、初期係数商と実剰余の忠実平坦性を合成する。
規約：distinguished 性と p 正則性以外の δ 仮定は不要。族の有限性も要求しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実導来還元との比較への剰余入力。 -/
theorem monicPrismaticRawResidue_faithfullyFlat_of_distinguished
    (hdp : D.IsDistinguished d) (hf : ∀ s, (f s).Monic)
    (hdeg : ∀ s, 0 < (f s).natDegree) :
    letI := monicPrismaticRawResidueAlgebraOfDistinguished D d f hpA hdp
    Module.FaithfullyFlat QA Res :=
  monicPrismaticRawResidue_faithfullyFlat D d f hpA
    (deltaRootSource_ghostMap_injective (σ := σ) hpA) hdp.unit hdp.unit_spec hf hdeg

end SerrePositivity.BhattScholze.Andre

end MonicPrismaticRawResidue

/-! ## 実商還元の H⁰ の元の係数商上の忠実平坦性

## 概要

有限正次数モニック族の実自由 δ 源商上の導来還元の H⁰ は、元の A/(p,d) 上忠実平坦。
BS 著者版 Remark 7.15（著者版 p.62）の係数作用を保つ剰余比較。

## 方針

H⁰ の実源商線形比較を係数商へ制限し、明示した raw 剰余の標準係数作用と一致させる。
原典の BS 著者版 Proposition 7.11 を用いる証明とは異なる経路の計算。

## 規約

一般 (p,d) 商に沿う実還元を使う。Koszul 還元との無条件な同一視はしない。

## 使われ方

元の係数環上の実導来還元の平坦性と、完備化後の離散性の入力。
-/

@[expose] public noncomputable section MonicPrismaticQuotientFlat

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A) {m : ℕ}
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => (fun t : σ => monicRelation (f t) t)
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q₀" => L₀ ⧸ K₀
local notation "q₀" => Ideal.Quotient.mk K₀
local notation "k₀" => Ideal.span {(p : A), d}
local notation "κ₀" => Ideal.Quotient.mk k₀
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

set_option maxHeartbeats 800000 in
-- 実商環上のホモロジーと複数の商作用を同時に照合するため。
/-- 概要：有限モニック族について、実導来商還元のH0は元のA/(p,d)上忠実平坦。
方針：実源商上の H⁰ 同型を元の係数商へ制限し、係数の代表元公式で忠実平坦性を移す。
規約：有限全列挙、モニック性、正次数、p 正則性、δ(d) の単元性を要求する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の A/(p,d) 上の実導来剰余入力。 -/
theorem monicPrismaticSourceQuotientDerivedH0_faithfullyFlat (s : Fin m ≃ σ)
    (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    Module.FaithfullyFlat (A ⧸ k₀)
      ((ModuleCat.restrictScalars (deltaRootSourceQuotientCoefficientMap (σ := σ) d)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
          (MonicPrismaticSourceQuotientDerived D d f).obj)) := by
  have hg := deltaRootSource_ghostMap_injective (σ := σ) hpA
  let := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
  let : Module Q₀ Res₀ := Algebra.toModule
  let := monicPrismaticRawResidueBaseAlgebra D d f hpA hg v hv
  let H := (DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
    (MonicPrismaticSourceQuotientDerived D d f).obj
  let M := (ModuleCat.restrictScalars
    (deltaRootSourceQuotientCoefficientMap (σ := σ) d)).obj H
  let eQ := monicPrismaticSourceQuotientDerivedH0Iso D d f s hf hpA v hv
  let e : M ≃ₗ[A ⧸ k₀] Res₀ :=
    { toFun := eQ.hom.hom
      invFun := eQ.inv.hom
      left_inv := fun x => congrArg (fun f => f.hom x) eQ.hom_inv_id
      right_inv := fun x => congrArg (fun f => f.hom x) eQ.inv_hom_id
      map_add' := eQ.hom.hom.map_add
      map_smul' := by
        intro s x
        obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective s
        change H at x
        have h := eQ.hom.hom.map_smul
          (deltaRootSourceQuotientCoefficientMap (σ := σ) d (κ₀ a)) x
        change eQ.hom.hom ((deltaRootSourceQuotientCoefficientMap (σ := σ) d (κ₀ a)) • x) =
          monicPrismaticSourceQuotientResidueMap D d f
            (deltaRootSourceQuotientCoefficientMap (σ := σ) d (κ₀ a)) * eQ.hom.hom x at h
        rw [deltaRootSourceQuotientCoefficientMap_mk,
          monicPrismaticSourceQuotientResidueMap_mk, deltaDivisionSourceEval_C] at h
        change eQ.hom.hom ((deltaRootSourceQuotientCoefficientMap (σ := σ) d (κ₀ a)) • x) =
          monicPrismaticRawResidueBaseMap D d f hpA hg v hv (κ₀ a) * eQ.hom.hom x
        rw [deltaRootSourceQuotientCoefficientMap_mk,
          monicPrismaticRawResidueBaseMap_mk]
        exact h }
  have := monicPrismaticRawResidue_faithfullyFlat D d f hpA hg v hv hf hdeg
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e


end SerrePositivity.BhattScholze.Andre

end MonicPrismaticQuotientFlat

/-! ## 元の係数環上の実 (p,d) 還元と raw 残余商

## 概要

有限正次数モニック族の f/d 源の実 (p,d) 還元は離散的で、H⁰ が元の A/(p,d) 上忠実平坦。
BS 著者版 Remark 7.15（著者版 p.62）の元の係数作用を保つ剰余計算。

## 方針

二重多項式係数包含の一般導来正方形比較を再利用し、実源商上で得た同型と忠実平坦性を移す。
原典の BS 著者版 Proposition 7.11 を使う証明とは異なる経路の計算。

## 規約

離散性には正次数は不要。完備化後の離散性は別工程。

## 使われ方

実逐次 p,d 完備化と、その生成元冪商への還元の入力。
-/

@[expose] public noncomputable section MonicPrismaticPDReduction

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A) {m : ℕ}
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => (fun t : σ => monicRelation (f t) t)
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q₀" => L₀ ⧸ K₀
local notation "I₀" => Ideal.span {(p : A), d}
local notation "R₀" => A ⧸ I₀
local notation "κ₀" => deltaRootSourceQuotientCoefficientMap (σ := σ) (p := p) d
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "ψ₀" => RingHom.comp (Ideal.Quotient.mk K₀) α₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀
local notation "MRes" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars κ₀)
  (ModuleCat.of Q₀ Res₀)

local notation "LCoef" => algebraMap A L₀
local notation "β₀" => deltaDivisionSourceEval E₀ c₀
local notation "Mα" => baseChangeScalarModule α₀
local notation "Mβ" => baseChangeScalarModule β₀
local notation "X₀" => boundedAboveDerivedTensor.obj
  (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα)

/-- 概要：一般モニック f/d 包の実二因子導来対象を元の係数環 A へ制限する。
方針：二重多項式係数包含に沿う既存の導来係数制限を適用する。
規約：有限性やモニック性は対象の定義には不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の元の係数環上の実 prismatic 源。 -/
abbrev MonicPrismaticSourceCoefficientObject := (boundedAboveDerivedRestrictScalars LCoef).obj X₀

set_option maxHeartbeats 800000 in
-- 実二因子の具体的な射影テンソルモデルと二重係数商の作用を同時に照合するため。
/-- 概要：元の A/(p,d) に沿う実還元は、実自由 δ 源商上の還元の係数制限と同型。
方針：二重多項式源に対する既存の一般導来係数正方形比較を再利用する。
規約：正方形比較自体にはモニック性も有限性も不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の raw 剰余の元の係数作用への比較。 -/
def monicPrismaticSourceCoefficientPDReductionIso :
    (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I₀)).obj
        (MonicPrismaticSourceCoefficientObject D d f) ≅
      (boundedAboveDerivedRestrictScalars κ₀).obj (MonicPrismaticSourceQuotientDerived D d f) :=
  deltaRootSourcePDDerivedSquareIso (p := p) (A := A) (σ := σ) d X₀
    (boundedAboveDerivedTensorModel
      (boundedAboveDerivedSingleFunctor.obj Mβ) (boundedAboveDerivedSingleFunctor.obj Mα))

local notation "Y₀" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk I₀))
  (MonicPrismaticSourceCoefficientObject D d f)

/-- 概要：元のA上の実モニック族添加対象の実(p,d)還元と、作用を制限したraw商のsingle比較。
方針：元の係数商への実正方形比較と、実源商上の正規化比較を合成する。
規約：有限全列挙、モニック性、p 正則性、δ(d) の単元性を使い、忠実性には正次数を追加する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実完備化後の剰余入力。 -/
def monicPrismaticSourceCoefficientPDResidueIso (s : Fin m ≃ σ) (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    Y₀ ≅ boundedAboveDerivedSingleFunctor.obj MRes := by
  letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact monicPrismaticSourceCoefficientPDReductionIso D d f ≪≫
    (boundedAboveDerivedRestrictScalars κ₀).mapIso
      (monicPrismaticSourceQuotientDerivedSingleIso D d f s hf hpA v hv) ≪≫
    ObjectProperty.isoMk _ ((derivedRestrictScalarsSingleIso κ₀ 0).app (ModuleCat.of Q₀ Res₀))

/-- 概要：元のA上の実還元のH0と、標準係数作用を制限したraw商の加群同型。
方針：元の係数商への実正方形比較と、実源商上の正規化比較を合成する。
規約：有限全列挙、モニック性、p 正則性、δ(d) の単元性を使い、忠実性には正次数を追加する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実完備化後の剰余入力。 -/
def monicPrismaticSourceCoefficientPDResidueH0Iso (s : Fin m ≃ σ) (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj (Y₀).obj ≅ MRes := by
  letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (monicPrismaticSourceCoefficientPDResidueIso D d f s hf hpA v hv)) ≪≫
    (realizedSingleH0Iso R₀).app MRes

/-- 概要：元のA上の実(p,d)還元の非零次数ホモロジーは零。
方針：元の係数商への実正方形比較と、実源商上の正規化比較を合成する。
規約：有限全列挙、モニック性、p 正則性、δ(d) の単元性を使い、忠実性には正次数を追加する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実完備化後の剰余入力。 -/
theorem monicPrismaticSourceCoefficientPDResidue_homology_isZero
    (s : Fin m ≃ σ) (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).obj (Y₀).obj) := by
  let := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
  let : Module Q₀ Res₀ := Algebra.toModule
  exact (derivedSingleHomology_isZero MRes i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (monicPrismaticSourceCoefficientPDResidueIso D d f s hf hpA v hv)))

/-- 概要：元のA上の実(p,d)還元のH0は、実係数商A/(p,d)上忠実平坦。
方針：元の係数商への実正方形比較と、実源商上の正規化比較を合成する。
規約：有限全列挙、モニック性、p 正則性、δ(d) の単元性を使い、忠実性には正次数を追加する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実完備化後の剰余入力。 -/
theorem monicPrismaticSourceCoefficientPDResidueH0_faithfullyFlat
    (s : Fin m ≃ σ) (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
    (hpA : Function.Injective (fun x : A => (p : A) * x))
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    Module.FaithfullyFlat R₀
      ((DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj (Y₀).obj) := by
  let e : (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj (Y₀).obj ≅
      (ModuleCat.restrictScalars κ₀).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Q₀) 0).obj
          (MonicPrismaticSourceQuotientDerived D d f).obj) :=
    (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso (monicPrismaticSourceCoefficientPDReductionIso D d f)) ≪≫
    (derivedRestrictScalarsHomologyIso κ₀ 0).app (MonicPrismaticSourceQuotientDerived D d f).obj
  have := monicPrismaticSourceQuotientDerivedH0_faithfullyFlat
    D d f s hf hdeg hpA v hv
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.toLinearEquiv

end SerrePositivity.BhattScholze.Andre

end MonicPrismaticPDReduction

/-! ## 実逐次 p,d 完備化後のモニック源の剰余

## 概要

有限正次数モニック族の f/d 源を p,d の順に実導来完備化した対象の実 (p,d) 還元は
離散的で、H⁰ は元の A/(p,d) 上忠実平坦。BS 著者版 Remark 7.15（著者版 p.62）の準備。

## 方針

p と d の個別の正則性により一般の逐次完備化単位比較を用い、元の実剰余計算へ戻す。
原典の BS 著者版 Proposition 7.11 を使う証明とは異なる経路の計算。

## 規約

d mod p の正則性は仮定しない。実完備化対象自体の離散性はまだ主張しない。

## 使われ方

冪零厚化と生成元冪商上の導来完備 Nakayama 判定へ渡す。
-/

@[expose] public noncomputable section MonicPrismaticIteratedResidue

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A) {m : ℕ}
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => (fun t : σ => monicRelation (f t) t)
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q₀" => L₀ ⧸ K₀
local notation "I₀" => Ideal.span {(p : A), d}
local notation "R₀" => A ⧸ I₀
local notation "q₀" => Ideal.Quotient.mk I₀
local notation "κ₀" => deltaRootSourceQuotientCoefficientMap (σ := σ) (p := p) d
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "ψ₀" => RingHom.comp (Ideal.Quotient.mk K₀) α₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀
local notation "X₀" => MonicPrismaticSourceCoefficientObject D d f
local notation "Cp" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)
local notation "Cd" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A d
local notation "Up" => DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)
local notation "Ud" => DerivedCompletion.boundedAboveDerivedCompletionUnit A d
local notation "MRes" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars κ₀)
  (ModuleCat.of Q₀ Res₀)

/-- 概要：一般モニック f/d 源を実 p 完備化してから実 d 完備化した対象。
方針：既存の二つの主元導来完備化関手を逐次適用する。
規約：モニック性・正則性は対象の定義には不要。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の prismatic envelope の実完備化への源。 -/
abbrev MonicPrismaticSourceIteratedPDCompletion := (Cd).obj ((Cp).obj X₀)

/-- 概要：p と d が係数環で個別に正則なら、逐次完備化の実 (p,d) 還元は元の実還元と同型。
方針：一般の主元完備化単位の二生成商比較を再利用する。
規約：d mod p の正則性は仮定しない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の完備化前後の実剰余比較。 -/
def monicPrismaticSourceIteratedPDReductionIso
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d) :
    (boundedAboveDerivedBaseChange q₀).obj (MonicPrismaticSourceIteratedPDCompletion D d f) ≅
      (boundedAboveDerivedBaseChange q₀).obj X₀ :=
  prismaticCoefficientIteratedCompletionPairIso (p : A) d hpA hd X₀

/-- 概要：実還元比較は、二つの標準完備化単位の合成の還元像の左逆。
方針：一般の逐次完備化比較の標準単位公式を使う。
規約：元の実係数作用と実対象を固定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の候補係数射との後続比較。 -/
theorem monicPrismaticSourceIteratedPDReductionIso_unit
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d) :
    (boundedAboveDerivedBaseChange q₀).map (((Up).app X₀) ≫ (Ud).app ((Cp).obj X₀)) ≫
      (monicPrismaticSourceIteratedPDReductionIso D d f hpA hd).hom = 𝟙 _ :=
  prismaticCoefficientIteratedCompletionPairIso_unit (p : A) d hpA hd X₀

/-- 概要：有限モニック族について、逐次主元完備化後の実還元は標準作用付きraw残余商のsingle対象。
方針：一般の逐次完備化の実剰余比較と、前工程の元の係数環上の raw 剰余比較を合成する。
規約：p と d の個別の正則性、有限モニック族を使い、忠実性には正次数を追加する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の生成元冪商の実還元への入力。 -/
def monicPrismaticSourceIteratedPDResidueIso (s : Fin m ≃ σ) (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    (boundedAboveDerivedBaseChange q₀).obj (MonicPrismaticSourceIteratedPDCompletion D d f) ≅
      boundedAboveDerivedSingleFunctor.obj MRes := by
  letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact monicPrismaticSourceIteratedPDReductionIso D d f hpA hd ≪≫
    monicPrismaticSourceCoefficientPDResidueIso D d f s hf hpA v hv

/-- 概要：raw比較は合成標準単位の実還元を、未完備対象のraw比較へ送る。
方針：一般の逐次完備化の実剰余比較と、前工程の元の係数環上の raw 剰余比較を合成する。
規約：p と d の個別の正則性、有限モニック族を使い、忠実性には正次数を追加する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の生成元冪商の実還元への入力。 -/
theorem monicPrismaticSourceIteratedPDResidueIso_unit (s : Fin m ≃ σ) (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    (boundedAboveDerivedBaseChange q₀).map (((Up).app X₀) ≫ (Ud).app ((Cp).obj X₀)) ≫
      (monicPrismaticSourceIteratedPDResidueIso D d f s hf hpA hd v hv).hom =
      (monicPrismaticSourceCoefficientPDResidueIso D d f s hf hpA v hv).hom := by
  let := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
  let : Module Q₀ Res₀ := Algebra.toModule
  simp only [monicPrismaticSourceIteratedPDResidueIso, Iso.trans_hom]
  rw [← Category.assoc, monicPrismaticSourceIteratedPDReductionIso_unit, Category.id_comp]

/-- 概要：逐次主元完備化後の実(p,d)還元の非零次数ホモロジーは零。
方針：一般の逐次完備化の実剰余比較と、前工程の元の係数環上の raw 剰余比較を合成する。
規約：p と d の個別の正則性、有限モニック族を使い、忠実性には正次数を追加する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の生成元冪商の実還元への入力。 -/
theorem monicPrismaticSourceIteratedPDResidue_homology_isZero
    (s : Fin m ≃ σ) (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).obj
      ((boundedAboveDerivedBaseChange q₀).obj
        (MonicPrismaticSourceIteratedPDCompletion D d f)).obj) :=
  (monicPrismaticSourceCoefficientPDResidue_homology_isZero
    D d f s hf hpA v hv i hi).of_iso
      ((DerivedCategory.homologyFunctor (ModuleCat R₀) i).mapIso
        (DerivedCategory.Minus.ι.mapIso
          (monicPrismaticSourceIteratedPDReductionIso D d f hpA hd)))

/-- 概要：逐次主元完備化後の実(p,d)還元のH0は、標準A/(p,d)上で忠実平坦。
方針：一般の逐次完備化の実剰余比較と、前工程の元の係数環上の raw 剰余比較を合成する。
規約：p と d の個別の正則性、有限モニック族を使い、忠実性には正次数を追加する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の生成元冪商の実還元への入力。 -/
theorem monicPrismaticSourceIteratedPDResidueH0_faithfullyFlat
    (s : Fin m ≃ σ) (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    Module.FaithfullyFlat R₀ ((DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj
      ((boundedAboveDerivedBaseChange q₀).obj
        (MonicPrismaticSourceIteratedPDCompletion D d f)).obj) := by
  let e : (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj
      ((boundedAboveDerivedBaseChange q₀).obj
        (MonicPrismaticSourceIteratedPDCompletion D d f)).obj ≅
      (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj
        ((boundedAboveDerivedBaseChange q₀).obj X₀).obj :=
    (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso (monicPrismaticSourceIteratedPDReductionIso D d f hpA hd))
  have := monicPrismaticSourceCoefficientPDResidueH0_faithfullyFlat
    D d f s hf hdeg hpA v hv
  exact Module.FaithfullyFlat.of_linearEquiv _ _ e.toLinearEquiv

end SerrePositivity.BhattScholze.Andre

end MonicPrismaticIteratedResidue

/-! ## モニック源の実逐次完備性と生成元冪商の p 完備性

## 概要

実逐次 p,d 完備化は両方向に導来完備で、正則な d の冪商への実還元も商環上で p 導来完備。
BS 著者版 Remark 7.15（著者版 p.62）の生成元冪商の離散性の準備。

## 方針

完備性の錐と塔極限での閉性、正則冪商の Koszul 比較、G8 の係数制限の標準単位比較を使う。
原典の BS 著者版 Proposition 7.11 を使う証明とは異なる経路の計算。

## 規約

元の f/d 源と同じ実逐次対象を扱う。これらの完備性にはモニック性・正次数・有限性は不要。

## 使われ方

生成元冪商への実還元を、導来完備 Nakayama の同じ対象として固定する。
-/

@[expose] public noncomputable section MonicPrismaticSourceComplete

set_option backward.isDefEq.respectTransparency false
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)

/-- 概要：実p完備化後に実d完備化を施した具体的モニック族添加対象は、なおp導来完備。
方針：既存の完備性の錐・塔極限での閉性と、係数制限の標準単位比較を使う。
規約：対象の定義以外にはモニック性や有限性を使わない。冪商の比較には d の正則性を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の冪商上の導来完備 Nakayama 入力。 -/
theorem monicPrismaticSourceIteratedPDCompletion_isComplete_p :
    DerivedCompletion.IsComplete A (p : A)
      (MonicPrismaticSourceIteratedPDCompletion D d f).obj := by
  let X := MonicPrismaticSourceCoefficientObject D d f
  let Y := (DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj X
  have hY : DerivedCompletion.IsComplete A (p : A) Y.obj :=
    DerivedCompletion.derivedComplexCompletionFunctor_isComplete A (p : A) X.obj
  let K := DerivedCategory.Q.objPreimage Y.obj
  let eK : DerivedCategory.Q.obj K ≅ Y.obj := DerivedCategory.Q.objObjPreimageIso Y.obj
  have hK : DerivedCompletion.IsComplete A (p : A) (DerivedCategory.Q.obj K) :=
    DerivedCompletion.isComplete_of_iso A (p : A) eK.symm hY
  have hstage (n : ℕ) : DerivedCompletion.IsComplete A (p : A)
      (DerivedCategory.Q.obj (DerivedCompletion.complexPowerKoszulStage A d K n)) :=
    DerivedCompletion.isComplete_Q_mappingCone A (p : A)
      (smulId (d ^ n) K) hK hK
  have hC : DerivedCompletion.IsComplete A (p : A)
      (DerivedCompletion.complexCompletionObject A d K) :=
    DerivedCompletion.isComplete_complexTowerHomotopyLimitObject_of_stages A (p : A)
      (DerivedCompletion.complexPowerKoszulStage A d K)
      (DerivedCompletion.complexPowerKoszulTransition A d K) hstage
  let e : DerivedCompletion.complexCompletionObject A d K ≅
      (MonicPrismaticSourceIteratedPDCompletion D d f).obj :=
    (DerivedCompletion.derivedComplexCompletionComparison A d).symm.app K ≪≫
      (DerivedCompletion.derivedComplexCompletionFunctor A d).mapIso eK
  exact DerivedCompletion.isComplete_of_iso A (p : A) e hC

/-- 概要：同じ具体的逐次対象は、最後の主元完備化によりd導来完備。
方針：既存の完備性の錐・塔極限での閉性と、係数制限の標準単位比較を使う。
規約：対象の定義以外にはモニック性や有限性を使わない。冪商の比較には d の正則性を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の冪商上の導来完備 Nakayama 入力。 -/
theorem monicPrismaticSourceIteratedPDCompletion_isComplete_d :
    DerivedCompletion.IsComplete A d
      (MonicPrismaticSourceIteratedPDCompletion D d f).obj :=
  DerivedCompletion.derivedComplexCompletionFunctor_isComplete A d
    ((DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)).obj
      (MonicPrismaticSourceCoefficientObject D d f)).obj

local notation "X₀" => MonicPrismaticSourceIteratedPDCompletion D d f

/-- 概要：正則dの実冪商への基底変更を制限すると、候補の実dⁿ Koszul錐になる。
方針：既存の完備性の錐・塔極限での閉性と、係数制限の標準単位比較を使う。
規約：対象の定義以外にはモニック性や有限性を使わない。冪商の比較には d の正則性を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の冪商上の導来完備 Nakayama 入力。 -/
def monicPrismaticSourceGeneratorPowerReductionKoszulIso (hd : IsSMulRegular A d) (n : ℕ) :
    ((boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X₀)).obj ≅
        (DerivedCompletion.derivedScalarConeFunctor A (d ^ n)).obj (X₀).obj :=
  restrictedDerivedQuotientKoszulIso (d ^ n) (hd.pow n) X₀

/-- 概要：正則dの任意冪商での実導来還元をAへ制限した対象は、p導来完備。
方針：既存の完備性の錐・塔極限での閉性と、係数制限の標準単位比較を使う。
規約：対象の定義以外にはモニック性や有限性を使わない。冪商の比較には d の正則性を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の冪商上の導来完備 Nakayama 入力。 -/
theorem monicPrismaticSourceGeneratorPowerReduction_isComplete_p
    (hd : IsSMulRegular A d) (n : ℕ) :
    DerivedCompletion.IsComplete A (p : A)
      (((boundedAboveDerivedRestrictScalars (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj
        ((boundedAboveDerivedBaseChange
          (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj X₀)).obj) := by
  let K := DerivedCategory.Q.objPreimage (X₀).obj
  let eK : DerivedCategory.Q.obj K ≅ (X₀).obj := DerivedCategory.Q.objObjPreimageIso (X₀).obj
  have hK : DerivedCompletion.IsComplete A (p : A) (DerivedCategory.Q.obj K) :=
    DerivedCompletion.isComplete_of_iso A (p : A) eK.symm
      (monicPrismaticSourceIteratedPDCompletion_isComplete_p D d f)
  have hC := DerivedCompletion.isComplete_Q_mappingCone A (p : A) (smulId (d ^ n) K) hK hK
  let e := monicPrismaticSourceGeneratorPowerReductionKoszulIso D d f hd n ≪≫
    (DerivedCompletion.derivedScalarConeFunctor A (d ^ n)).mapIso eK.symm ≪≫
      (DerivedCompletion.derivedScalarConeComparison A (d ^ n)).app K
  exact DerivedCompletion.isComplete_of_iso A (p : A) e.symm hC

/-- 概要：正則生成元の任意冪商への実還元は、その商環上でp導来完備。n=0も含む。
方針：既存の完備性の錐・塔極限での閉性と、係数制限の標準単位比較を使う。
規約：対象の定義以外にはモニック性や有限性を使わない。冪商の比較には d の正則性を使う。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の冪商上の導来完備 Nakayama 入力。 -/
theorem monicPrismaticSourceGeneratorPowerReduction_isComplete_over_quotient
    (hd : IsSMulRegular A d) (n : ℕ) :
    IsComplete (A ⧸ Ideal.span {d ^ n}) (p : A ⧸ Ideal.span {d ^ n})
      ((boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))).obj
        (MonicPrismaticSourceIteratedPDCompletion D d f)).obj := by
  let q := Ideal.Quotient.mk (Ideal.span {d ^ n})
  let T := A ⧸ Ideal.span {d ^ n}
  let Y := ((boundedAboveDerivedBaseChange q).obj
    (MonicPrismaticSourceIteratedPDCompletion D d f)).obj
  let F := derivedRestrictScalars q
  have hR : IsComplete A (p : A) (F.obj Y) :=
    monicPrismaticSourceGeneratorPowerReduction_isComplete_p D d f hd n
  have hunitR : IsIso ((derivedComplexCompletionUnit A (p : A)).app (F.obj Y)) :=
    derivedComplexCompletionUnit_isIso_of_isComplete A (p : A) (F.obj Y) hR
  let e := derivedRestrictionCompletionIso q (p : A)
  have hc : IsIso (F.map ((derivedComplexCompletionUnit T (q (p : A))).app Y) ≫
      e.hom.app Y) := by
    rw [derivedRestrictionCompletionIso_unit]
    exact hunitR
  have hm : IsIso (F.map ((derivedComplexCompletionUnit T (q (p : A))).app Y)) :=
    IsIso.of_isIso_comp_right _ (e.hom.app Y)
  have hS : IsIso ((derivedComplexCompletionUnit T (q (p : A))).app Y) :=
    isIso_of_reflects_iso _ F
  have hcomplete := (isComplete_iff_derivedComplexCompletionUnit_isIso T (q (p : A)) Y).mpr hS
  simpa only [map_natCast] using hcomplete


end SerrePositivity.BhattScholze.Andre

end MonicPrismaticSourceComplete

/-! ## モニック源の生成元冪商の標準冪零還元

## 概要

実逐次 p,d 完備化の A/(p,dⁿ) 還元を標準冪零商でさらに還元すると、
raw 剰余の係数作用を保つ single になる。BS 著者版 Remark 7.15（著者版 p.62）の冪商計算。

## 方針

一般の冪零商・合成係数拡大の比較と、前工程の実 (p,d) 還元比較を合成する。
原典の BS 著者版 Proposition 7.11 を使う証明とは異なる経路の計算。

## 規約

n は正とする。二つの元の個別の正則性を使い、正則列とは仮定しない。

## 使われ方

冪零還元からの純性・平坦性の既存判定 G10 へ、同じ実対象の入力を渡す。
-/

@[expose] public noncomputable section MonicPrismaticCanonicalPowerResidue

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A) (n : ℕ) (hn : 0 < n) {m : ℕ}
local notation "P₀" => MvPolynomial σ A
local notation "L₀" => RelativeFreeDeltaRing (R := P₀) σ
local notation "E₀" => polynomialRankOneDeltaStructure σ D
local notation "c₀" => (fun t : σ => monicRelation (f t) t)
local notation "K₀" => Ideal.span {(p : L₀), MvPolynomial.C (MvPolynomial.C d)}
local notation "Q₀" => L₀ ⧸ K₀
local notation "I₀" => Ideal.span {(p : A), d}
local notation "R₀" => A ⧸ I₀
local notation "q₀" => Ideal.Quotient.mk I₀
local notation "κ₀" => deltaRootSourceQuotientCoefficientMap (σ := σ) (p := p) d
local notation "α₀" => deltaDivisionSourceMap (σ := σ) E₀ (MvPolynomial.C d)
local notation "ψ₀" => RingHom.comp (Ideal.Quotient.mk K₀) α₀
local notation "Res₀" => DeltaAdjoinDivisionResidue E₀ (MvPolynomial.C d) c₀
local notation "X₀" => MonicPrismaticSourceIteratedPDCompletion D d f
local notation "MRes" => CategoryTheory.Functor.obj (ModuleCat.restrictScalars κ₀)
  (ModuleCat.of Q₀ Res₀)

local notation "qₙ" =>
  Ideal.Quotient.mk (Ideal.span (Set.insert (p : A) (Set.singleton (d ^ n))))
local notation "rₙ" => prismaticPowerResidueMap (p : A) d n hn
local notation "Z₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange rₙ)
  (CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange qₙ) X₀)

local notation "Tₙ" => A ⧸ Ideal.span (Set.insert (p : A) (Set.singleton (d ^ n)))
local notation "Kₙ" => prismaticPowerResidueIdeal (p : A) d n
local notation "Sₙ" => Tₙ ⧸ Kₙ
local notation "eₙ" => prismaticPowerResidueQuotientEquiv (p : A) d n hn
local notation "Y₀" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange qₙ) X₀
local notation "W₀" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk Kₙ)) Y₀
local notation "MCan" => CategoryTheory.Functor.obj
  (ModuleCat.restrictScalars (RingEquiv.toRingHom eₙ)) MRes

/-- 概要：G10の標準冪零商による実還元は、商環上の標準raw加群のsingle対象。
方針：標準冪零商の一般比較と、元の (p,d) 還元の実 single 比較を合成する。
規約：有限モニック族、p と d の個別の正則性、δ(d) の単元性を使い、忠実性には正次数を追加する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の冪零厚化による実剰余の離散・平坦性。 -/
def monicPrismaticSourceCanonicalPowerResidueIso (s : Fin m ≃ σ) (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
    letI : Module Q₀ Res₀ := Algebra.toModule
    W₀ ≅ boundedAboveDerivedSingleFunctor.obj MCan := by
  letI := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
  letI : Module Q₀ Res₀ := Algebra.toModule
  exact prismaticPowerResidueCanonicalDerivedIso (p : A) d n hn Y₀ ≪≫
    (boundedAboveDerivedRestrictScalars (eₙ).toRingHom).mapIso
      ((prismaticPowerResidueDerivedCompositionIso (p : A) d n hn X₀).symm ≪≫
        monicPrismaticSourceIteratedPDResidueIso D d f s hf hpA hd v hv) ≪≫
    ObjectProperty.isoMk _ ((derivedRestrictScalarsSingleIso (eₙ).toRingHom 0).app MRes)

include hn in
/-- 概要：標準冪零商による実還元の非零次数ホモロジーは零。
方針：標準冪零商の一般比較と、元の (p,d) 還元の実 single 比較を合成する。
規約：有限モニック族、p と d の個別の正則性、δ(d) の単元性を使い、忠実性には正次数を追加する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の冪零厚化による実剰余の離散・平坦性。 -/
theorem monicPrismaticSourceCanonicalPowerResidue_homology_isZero
    (s : Fin m ≃ σ) (hf : ∀ t, (f t).Monic)
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d)
    (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Sₙ) i).obj (W₀).obj) := by
  let := (monicPrismaticSourceQuotientResidueMap D d f).toAlgebra
  let : Module Q₀ Res₀ := Algebra.toModule
  exact (derivedSingleHomology_isZero MCan i hi).of_iso
    ((DerivedCategory.homologyFunctor (ModuleCat Sₙ) i).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (monicPrismaticSourceCanonicalPowerResidueIso
          D d f n hn s hf hpA hd v hv)))

include hn in
/-- 概要：標準冪零商による実還元のH0は、その正確な商環上で忠実平坦。
方針：標準冪零商の一般比較と、元の (p,d) 還元の実 single 比較を合成する。
規約：有限モニック族、p と d の個別の正則性、δ(d) の単元性を使い、忠実性には正次数を追加する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の冪零厚化による実剰余の離散・平坦性。 -/
theorem monicPrismaticSourceCanonicalPowerResidueH0_faithfullyFlat
    (s : Fin m ≃ σ) (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
    (hpA : Function.Injective (fun x : A => (p : A) * x)) (hd : IsSMulRegular A d)
    (v : Aˣ) (hv : (v : A) = D.delta d) :
    Module.FaithfullyFlat Sₙ
      ((DerivedCategory.homologyFunctor (ModuleCat Sₙ) 0).obj (W₀).obj) := by
  let M := (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj (Z₀).obj
  let eH : (DerivedCategory.homologyFunctor (ModuleCat Sₙ) 0).obj (W₀).obj ≅
      (ModuleCat.restrictScalars (eₙ).toRingHom).obj M :=
    (DerivedCategory.homologyFunctor (ModuleCat Sₙ) 0).mapIso
        (DerivedCategory.Minus.ι.mapIso
          (prismaticPowerResidueCanonicalDerivedIso (p : A) d n hn Y₀)) ≪≫
      (derivedRestrictScalarsHomologyIso (eₙ).toRingHom 0).app (Z₀).obj
  let := (eₙ).toRingHom.toAlgebra
  let : Module Sₙ M := Module.compHom M (eₙ).toRingHom
  let : IsScalarTower Sₙ R₀ M := IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let eA : Sₙ ≃ₐ[Sₙ] R₀ :=
    AlgEquiv.ofBijective (Algebra.ofId Sₙ R₀) (eₙ).bijective
  have : Module.FaithfullyFlat Sₙ R₀ :=
    Module.FaithfullyFlat.of_linearEquiv Sₙ Sₙ eA.symm.toLinearEquiv
  have : Module.FaithfullyFlat R₀ M := by
    let N := (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).obj
      ((boundedAboveDerivedBaseChange q₀).obj X₀).obj
    let eM : M ≅ N := (DerivedCategory.homologyFunctor (ModuleCat R₀) 0).mapIso
      (DerivedCategory.Minus.ι.mapIso
        (prismaticPowerResidueDerivedCompositionIso (p : A) d n hn X₀).symm)
    have : Module.FaithfullyFlat R₀ N :=
      monicPrismaticSourceIteratedPDResidueH0_faithfullyFlat D d f s hf hdeg hpA hd v hv
    exact Module.FaithfullyFlat.of_linearEquiv R₀ N eM.toLinearEquiv
  have : Module.FaithfullyFlat Sₙ M := Module.FaithfullyFlat.trans Sₙ R₀ M
  exact Module.FaithfullyFlat.of_linearEquiv Sₙ M eH.toLinearEquiv

end SerrePositivity.BhattScholze.Andre

end MonicPrismaticCanonicalPowerResidue

/-! ## モニック f/d 源と raw 包の実完備化比較

## 概要

一般モニック f/d 源の実 H⁰ を、同じ係数作用の raw 包およびその実完備化へ比較する。
BS 著者版 Remark 7.15（著者版 p.62）の raw PD 環との比較の準備。

## 方針

一般 δ 除算の通常テンソル表示、標準 augmentation、実係数制限と完備化の既存比較を再利用する。
原典の BS 著者版 Proposition 7.11 を使う経路とは異なる、具体的な元の係数作用を保つ計算。

## 規約

この H⁰ 比較にはモニック性・正次数・有限性は不要。高次ホモロジー消滅は別の証明を使う。

## 使われ方

実完備化源の離散性と組み合わせ、元の係数射の完全忠実平坦性を raw PD 環へ移す。
-/

@[expose] public noncomputable section MonicPrismaticRawSourceComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
local notation "P" => MvPolynomial σ A
local notation "L" => RelativeFreeDeltaRing (R := P) σ
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun t : σ => monicRelation (f t) t)
local notation "α" => deltaDivisionSourceMap (σ := σ) E (MvPolynomial.C d)
local notation "β" => deltaDivisionSourceEval E r
local notation "Mβ" => baseChangeScalarModule β
local notation "Mα" => baseChangeScalarModule α
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "X" => boundedAboveDerivedTensor.obj
  (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα)
local notation "C₀" => algebraMap A L

/-- 概要：raw包に、評価βを経由する元の実源L作用を明示した加群対象。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def MonicPrismaticSourceRawModule : ModuleCat.{u} L := by
  let := deltaDivisionSourceRawAlgebra E (MvPolynomial.C d) r
  let : Module L Raw := Algebra.toModule
  exact ModuleCat.of L Raw

/-- 概要：通常二因子テンソルとraw包は、元の実源L上で線形同型。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def monicPrismaticSourceOrdinaryTensorRawIso :
    (tensorLeft Mβ).obj Mα ≅ MonicPrismaticSourceRawModule D d f := by
  let := deltaDivisionSourceEvaluationAlgebra E r
  let := deltaDivisionSourceTargetAlgebra (σ := σ) E (MvPolynomial.C d)
  let : Module L L := Algebra.toModule
  let := deltaDivisionSourceRawAlgebra E (MvPolynomial.C d) r
  let : Module L Raw := Algebra.toModule
  let e : P ⊗[L] L ≃ₐ[L] Raw :=
    AlgEquiv.ofRingEquiv (f := deltaDivisionSourceTensorEquiv E (MvPolynomial.C d) r) (by
      intro x
      change deltaDivisionSourceTensorEquiv E (MvPolynomial.C d) r
        (β x ⊗ₜ[L] 1) = (deltaAdjoinDivisionMap E (MvPolynomial.C d) r) (β x)
      rw [deltaDivisionSourceTensorEquiv_tmul, map_one, mul_one])
  exact e.toLinearEquiv.toModuleIso

set_option maxHeartbeats 800000 in
-- 二つの実係数作用と元の導来テンソル対象の型を同時に照合するため。
/-- 概要：元の実導来二因子源から、raw次数零対象への標準augmentation。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def monicPrismaticSourceRawAugmentation :
    X ⟶ boundedAboveDerivedSingleFunctor.obj (MonicPrismaticSourceRawModule D d f) := by
  let η : X ⟶ boundedAboveDerivedSingleFunctor.obj ((tensorLeft Mβ).obj Mα) :=
    ObjectProperty.homMk ((boundedAboveDerivedTensorModuleAugmentation (R := L) Mβ).app Mα)
  exact η ≫ boundedAboveDerivedSingleFunctor.map
    (monicPrismaticSourceOrdinaryTensorRawIso D d f).hom

set_option maxHeartbeats 800000 in
-- 二つの実係数作用と元の導来テンソル対象の型を同時に照合するため。
/-- 概要：元の実導来二因子源のH0と実源作用付きraw包の比較。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def monicPrismaticSourceRawH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat L) 0).obj (X).obj ≅
      MonicPrismaticSourceRawModule D d f :=
  (boundedAboveDerivedTensorModuleH0NatIso (R := L) Mβ).app Mα ≪≫
    monicPrismaticSourceOrdinaryTensorRawIso D d f

/-- 概要：raw標準augmentationはH0では同型である。高次の消滅はここでは主張しない。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem monicPrismaticSourceRawAugmentation_h0_isIso :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat L) 0).map
      (monicPrismaticSourceRawAugmentation D d f).hom) := by
  have := derivedTensorAugmentation_h0_isIso (R := L) Mβ Mα
  change IsIso ((DerivedCategory.homologyFunctor (ModuleCat L) 0).map
    (((boundedAboveDerivedTensorModuleAugmentation (R := L) Mβ).app Mα) ≫
      (DerivedCategory.singleFunctor (ModuleCat L) 0).map
        (monicPrismaticSourceOrdinaryTensorRawIso D d f).hom))
  rw [CategoryTheory.Functor.map_comp]
  infer_instance

/-- 概要：元のAへ係数制限したraw次数零対象。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
abbrev MonicPrismaticSourceRawCoefficientObject :=
  (boundedAboveDerivedRestrictScalars C₀).obj
    (boundedAboveDerivedSingleFunctor.obj (MonicPrismaticSourceRawModule D d f))

set_option maxHeartbeats 800000 in
-- 元のテンソル対象の係数制限と実ホモロジーの型を同時に照合するため。
/-- 概要：元のAへ係数制限した実導来源のH0も、raw包の同じ係数制限と同型。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def monicPrismaticSourceRawCoefficientH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (MonicPrismaticSourceCoefficientObject D d f).obj ≅
      (ModuleCat.restrictScalars C₀).obj (MonicPrismaticSourceRawModule D d f) :=
  (derivedRestrictScalarsHomologyIso C₀ 0).app (X).obj ≪≫
    (ModuleCat.restrictScalars C₀).mapIso (monicPrismaticSourceRawH0Iso D d f)

/-- 概要：元のA上の実導来源からraw次数零対象への、同じ実係数制限による射。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def monicPrismaticSourceRawCoefficientAugmentation :
    MonicPrismaticSourceCoefficientObject D d f ⟶ MonicPrismaticSourceRawCoefficientObject D d f :=
  (boundedAboveDerivedRestrictScalars C₀).map (monicPrismaticSourceRawAugmentation D d f)

local notation "Cp" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)
local notation "Cd" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A d
local notation "Up" => DerivedCompletion.boundedAboveDerivedCompletionUnit A (p : A)
local notation "Ud" => DerivedCompletion.boundedAboveDerivedCompletionUnit A d

/-- 概要：raw次数零対象へ元と同じp,d逐次実導来完備化を施した対象。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
abbrev MonicPrismaticSourceRawIteratedCompletion :=
  (Cd).obj ((Cp).obj (MonicPrismaticSourceRawCoefficientObject D d f))

/-- 概要：元の実逐次完備化源から、rawの同じ実逐次完備化への標準比較射。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def monicPrismaticSourceRawIteratedComparison :
    MonicPrismaticSourceIteratedPDCompletion D d f ⟶ MonicPrismaticSourceRawIteratedCompletion D d f :=
  (Cd).map ((Cp).map (monicPrismaticSourceRawCoefficientAugmentation D d f))

/-- 概要：完備化後の比較射は、元のp,d合成標準単位と可換。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem monicPrismaticSourceRawIteratedComparison_unit :
    ((Up).app (MonicPrismaticSourceCoefficientObject D d f) ≫
      (Ud).app ((Cp).obj (MonicPrismaticSourceCoefficientObject D d f))) ≫
        monicPrismaticSourceRawIteratedComparison D d f =
      monicPrismaticSourceRawCoefficientAugmentation D d f ≫
        ((Up).app (MonicPrismaticSourceRawCoefficientObject D d f) ≫
          (Ud).app ((Cp).obj (MonicPrismaticSourceRawCoefficientObject D d f))) := by
  let η := monicPrismaticSourceRawCoefficientAugmentation D d f
  have hp := (Up).naturality η
  have hd := (Ud).naturality ((Cp).map η)
  simp only [CategoryTheory.Functor.id_map] at hp hd
  dsimp only [monicPrismaticSourceRawIteratedComparison]
  rw [Category.assoc, ← hd, ← Category.assoc, ← hp, Category.assoc]

end SerrePositivity.BhattScholze.Andre

end MonicPrismaticRawSourceComparison

/-! ## モニック f/d 源と raw 包の実完備化比較

## 概要

一般モニック f/d 源の実 H⁰ を、同じ係数作用の raw 包およびその実完備化へ比較する。
BS 著者版 Remark 7.15（著者版 p.62）の raw PD 環との比較の準備。

## 方針

一般 δ 除算の通常テンソル表示、標準 augmentation、実係数制限と完備化の既存比較を再利用する。
原典の BS 著者版 Proposition 7.11 を使う経路とは異なる、具体的な元の係数作用を保つ計算。

## 規約

この H⁰ 比較にはモニック性・正次数・有限性は不要。高次ホモロジー消滅は別の証明を使う。

## 使われ方

実完備化源の離散性と組み合わせ、元の係数射の完全忠実平坦性を raw PD 環へ移す。
-/

@[expose] public noncomputable section MonicPrismaticRawCoefficients

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
local notation "P" => MvPolynomial σ A
local notation "L" => RelativeFreeDeltaRing (R := P) σ
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun t : σ => monicRelation (f t) t)
local notation "β" => deltaDivisionSourceEval E r
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "j" => deltaAdjoinDivisionMap E (MvPolynomial.C d) r
local notation "C₀" => algebraMap A L

/-- 概要：評価βを経由する制限作用と、raw環の標準A作用の恒等線形同型。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def monicPrismaticSourceRawCoefficientModuleIso :
    (ModuleCat.restrictScalars C₀).obj (MonicPrismaticSourceRawModule D d f) ≅
      ModuleCat.of A Raw := by
  let e : (ModuleCat.restrictScalars C₀).obj (MonicPrismaticSourceRawModule D d f) ≃ₗ[A] Raw :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro a x
        rw [RingHom.id_apply, ModuleCat.restrictScalars.smul_def]
        change Raw at x
        change j (β (MvPolynomial.C (MvPolynomial.C a))) * x = a • x
        rw [Algebra.smul_def, deltaDivisionSourceEval_C]
        rfl }
  exact e.toModuleIso

/-- 概要：元のAへの実係数制限後のraw対象を、標準A作用付きraw環の次数零対象へ戻す。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def monicPrismaticSourceRawCoefficientSingleIso :
    MonicPrismaticSourceRawCoefficientObject D d f ≅
      boundedAboveDerivedSingleFunctor.obj (ModuleCat.of A Raw) :=
  ObjectProperty.isoMk _
    ((derivedRestrictScalarsSingleIso C₀ 0).app (MonicPrismaticSourceRawModule D d f) ≪≫
      (DerivedCategory.singleFunctor (ModuleCat A) 0).mapIso
        (monicPrismaticSourceRawCoefficientModuleIso D d f))

set_option maxHeartbeats 800000 in
-- 元の導来テンソルと二つの係数制限を H⁰ の型に明示して照合するため。
/-- 概要：元の実導来源のH0は、標準A作用付きraw r/d環と線形同型。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def monicPrismaticSourceRawStandardH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (MonicPrismaticSourceCoefficientObject D d f).obj ≅ ModuleCat.of A Raw :=
  monicPrismaticSourceRawCoefficientH0Iso D d f ≪≫ monicPrismaticSourceRawCoefficientModuleIso D d f

end SerrePositivity.BhattScholze.Andre

end MonicPrismaticRawCoefficients

/-! ## モニック f/d 源と raw 包の実完備化比較

## 概要

一般モニック f/d 源の実 H⁰ を、同じ係数作用の raw 包およびその実完備化へ比較する。
BS 著者版 Remark 7.15（著者版 p.62）の raw PD 環との比較の準備。

## 方針

一般 δ 除算の通常テンソル表示、標準 augmentation、実係数制限と完備化の既存比較を再利用する。
原典の BS 著者版 Proposition 7.11 を使う経路とは異なる、具体的な元の係数作用を保つ計算。

## 規約

この H⁰ 比較にはモニック性・正次数・有限性は不要。高次ホモロジー消滅は別の証明を使う。

## 使われ方

実完備化源の離散性と組み合わせ、元の係数射の完全忠実平坦性を raw PD 環へ移す。
-/

@[expose] public noncomputable section MonicPrismaticSourceNonpositive

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
local notation "P" => MvPolynomial σ A
local notation "L" => RelativeFreeDeltaRing (R := P) σ
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun t : σ => monicRelation (f t) t)
local notation "α" => deltaDivisionSourceMap (σ := σ) E (MvPolynomial.C d)
local notation "β" => deltaDivisionSourceEval E r
local notation "Mβ" => baseChangeScalarModule β
local notation "Mα" => baseChangeScalarModule α
local notation "X" => CategoryTheory.Functor.obj boundedAboveDerivedTensor
  (boundedAboveDerivedSingleFunctor.obj Mβ, boundedAboveDerivedSingleFunctor.obj Mα)
local notation "C₀" => algebraMap A L

set_option maxHeartbeats 800000 in
-- 元の係数作用を保って具体的な非正射影テンソルモデルを照合するため。
/-- 概要：同じ元の実A対象は非正次数の対象であり、離散性や完備性は仮定しない。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem monicPrismaticSourceCoefficient_isLE_zero :
    (MonicPrismaticSourceCoefficientObject D d f).obj.IsLE 0 := by
  let Pβ := projectiveResolutionDerivedModel (projectiveResolution Mβ)
  let Pα := projectiveResolutionDerivedModel (projectiveResolution Mα)
  let K := cochainTensor Pβ.complex Pα.complex
  let KR : CochainComplex (ModuleCat A) ℤ :=
    ((ModuleCat.restrictScalars C₀).mapHomologicalComplex (.up ℤ)).obj K
  have hβ : Pβ.complex.IsStrictlyLE 0 := Pβ.bounded
  have hα : Pα.complex.IsStrictlyLE 0 := Pα.bounded
  have hK : K.IsStrictlyLE 0 := by
    simpa only [add_zero] using cochainTensor_isStrictlyLE Pβ.complex Pα.complex 0 0
  have hKR : KR.IsStrictlyLE 0 := by
    apply (CochainComplex.isStrictlyLE_iff _ _).mpr
    intro i hi
    change IsZero ((ModuleCat.restrictScalars C₀).obj (K.X i))
    exact (ModuleCat.restrictScalars C₀).map_isZero (K.isZero_of_isStrictlyLE 0 i hi)
  let e : (MonicPrismaticSourceCoefficientObject D d f).obj ≅ DerivedCategory.Q.obj KR :=
    (derivedRestrictScalars C₀).mapIso
        (boundedAboveDerivedTensorModelIso
          (boundedAboveDerivedSingleFunctor.obj Mβ)
          (boundedAboveDerivedSingleFunctor.obj Mα) Pβ Pα) ≪≫
      (derivedRestrictScalarsFactors C₀).app K
  exact DerivedCategory.TStructure.t.isLE_of_iso e.symm 0

/-- 概要：元Aへ制限した同じ実二因子源は、全正次数でホモロジーが消える。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem monicPrismaticSourceCoefficient_homology_isZero_positive (i : ℤ) (hi : 0 < i) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat A) i).obj
      (MonicPrismaticSourceCoefficientObject D d f).obj) :=
  (DerivedCategory.isLE_iff _ _).mp (monicPrismaticSourceCoefficient_isLE_zero D d f) i hi

/-- 概要：同じaugmentationの終域である係数制限raw singleも非正次数である。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem monicPrismaticSourceRawCoefficient_isLE_zero :
    (MonicPrismaticSourceRawCoefficientObject D d f).obj.IsLE 0 := by
  let e : (MonicPrismaticSourceRawCoefficientObject D d f).obj ≅
      (DerivedCategory.singleFunctor (ModuleCat A) 0).obj
        ((ModuleCat.restrictScalars C₀).obj (MonicPrismaticSourceRawModule D d f)) :=
    (derivedRestrictScalarsSingleIso C₀ 0).app (MonicPrismaticSourceRawModule D d f)
  exact DerivedCategory.TStructure.t.isLE_of_iso e.symm 0

/-- 概要：元Aへ制限した標準augmentationそのものも、H0に同型を誘導する。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem monicPrismaticSourceRawCoefficientAugmentation_h0_isIso :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat A) 0).map
      (monicPrismaticSourceRawCoefficientAugmentation D d f).hom) := by
  let η := (monicPrismaticSourceRawAugmentation D d f).hom
  let H := DerivedCategory.homologyFunctor (ModuleCat A) 0
  let e := derivedRestrictScalarsHomologyIso C₀ 0
  have hf : IsIso ((DerivedCategory.homologyFunctor (ModuleCat L) 0).map η) :=
    monicPrismaticSourceRawAugmentation_h0_isIso D d f
  have hn := e.hom.naturality η
  simp only [Functor.comp_map] at hn
  have he : IsIso (H.map ((derivedRestrictScalars C₀).map η) ≫ e.hom.app _) := by
    rw [hn]
    infer_instance
  change IsIso (H.map ((derivedRestrictScalars C₀).map η))
  exact IsIso.of_isIso_comp_right _ (e.hom.app _)

end SerrePositivity.BhattScholze.Andre

end MonicPrismaticSourceNonpositive

/-! ## モニック f/d 源と raw 包の実完備化比較

## 概要

一般モニック f/d 源の実 H⁰ を、同じ係数作用の raw 包およびその実完備化へ比較する。
BS 著者版 Remark 7.15（著者版 p.62）の raw PD 環との比較の準備。

## 方針

一般 δ 除算の通常テンソル表示、標準 augmentation、実係数制限と完備化の既存比較を再利用する。
原典の BS 著者版 Proposition 7.11 を使う経路とは異なる、具体的な元の係数作用を保つ計算。

## 規約

この H⁰ 比較にはモニック性・正次数・有限性は不要。高次ホモロジー消滅は別の証明を使う。

## 使われ方

実完備化源の離散性と組み合わせ、元の係数射の完全忠実平坦性を raw PD 環へ移す。
-/

@[expose] public noncomputable section MonicPrismaticSourceCompletionH0

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
local notation "Cp" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A (p : A)
local notation "Cd" => DerivedCompletion.boundedAboveDerivedCompletionFunctor A d

/-- 概要：元の実係数源のp,d逐次実完備化も非正である。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem monicPrismaticSourceIteratedPDCompletion_isLE_zero :
    (MonicPrismaticSourceIteratedPDCompletion D d f).obj.IsLE 0 := by
  apply DerivedCompletion.boundedAboveDerivedCompletionFunctor_isLE A d _ 0
  exact DerivedCompletion.boundedAboveDerivedCompletionFunctor_isLE A (p : A) _ 0
    (monicPrismaticSourceCoefficient_isLE_zero D d f)

/-- 概要：raw係数対象の同じp,d逐次実完備化も非正である。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem monicPrismaticSourceRawIteratedCompletion_isLE_zero :
    (MonicPrismaticSourceRawIteratedCompletion D d f).obj.IsLE 0 := by
  apply DerivedCompletion.boundedAboveDerivedCompletionFunctor_isLE A d _ 0
  exact DerivedCompletion.boundedAboveDerivedCompletionFunctor_isLE A (p : A) _ 0
    (monicPrismaticSourceRawCoefficient_isLE_zero D d f)

/-- 概要：同じ元のaugmentationは、実p完備化後にもH0同型を誘導する。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem monicPrismaticSourceRawPComparison_h0_isIso :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      (((Cp).map (monicPrismaticSourceRawCoefficientAugmentation D d f)).hom)) := by
  exact DerivedCompletion.boundedAboveDerivedCompletion_h0_map_isIso A (p : A)
    (monicPrismaticSourceRawCoefficientAugmentation D d f)
    (monicPrismaticSourceCoefficient_isLE_zero D d f)
    (monicPrismaticSourceRawCoefficient_isLE_zero D d f)
    (monicPrismaticSourceRawCoefficientAugmentation_h0_isIso D d f)

/-- 概要：既存の標準逐次完備化比較射そのものがH0同型を誘導する。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem monicPrismaticSourceRawIteratedComparison_h0_isIso :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
      (monicPrismaticSourceRawIteratedComparison D d f).hom) := by
  exact DerivedCompletion.boundedAboveDerivedCompletion_h0_map_isIso A d
    ((Cp).map (monicPrismaticSourceRawCoefficientAugmentation D d f))
    (DerivedCompletion.boundedAboveDerivedCompletionFunctor_isLE A (p : A) _ 0
      (monicPrismaticSourceCoefficient_isLE_zero D d f))
    (DerivedCompletion.boundedAboveDerivedCompletionFunctor_isLE A (p : A) _ 0
      (monicPrismaticSourceRawCoefficient_isLE_zero D d f))
    (monicPrismaticSourceRawPComparison_h0_isIso D d f)

/-- 概要：実逐次源のH0とrawの実逐次完備化のH0を、同じ標準比較射で同定する。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def monicPrismaticSourceRawIteratedH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        (MonicPrismaticSourceIteratedPDCompletion D d f).obj ≅
      (DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).obj
        (MonicPrismaticSourceRawIteratedCompletion D d f).obj := by
  let := monicPrismaticSourceRawIteratedComparison_h0_isIso D d f
  exact asIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) 0).map
    (monicPrismaticSourceRawIteratedComparison D d f).hom)

end SerrePositivity.BhattScholze.Andre

end MonicPrismaticSourceCompletionH0

/-! ## モニック f/d 源と raw 包の実完備化比較

## 概要

一般モニック f/d 源の実 H⁰ を、同じ係数作用の raw 包およびその実完備化へ比較する。
BS 著者版 Remark 7.15（著者版 p.62）の raw PD 環との比較の準備。

## 方針

一般 δ 除算の通常テンソル表示、標準 augmentation、実係数制限と完備化の既存比較を再利用する。
原典の BS 著者版 Proposition 7.11 を使う経路とは異なる、具体的な元の係数作用を保つ計算。

## 規約

この H⁰ 比較にはモニック性・正次数・有限性は不要。高次ホモロジー消滅は別の証明を使う。

## 使われ方

実完備化源の離散性と組み合わせ、元の係数射の完全忠実平坦性を raw PD 環へ移す。
-/

@[expose] public noncomputable section MonicPrismaticRawCompletionRestriction

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun t : σ => monicRelation (f t) t)
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "M" => CategoryTheory.Functor.obj
  (DerivedCategory.singleFunctor (ModuleCat Raw) 0) (ModuleCat.of Raw Raw)
local notation "Cp" => derivedComplexCompletionFunctor A (p : A)
local notation "Cd" => derivedComplexCompletionFunctor A d
local notation "Bp" => derivedComplexCompletionFunctor Raw (c (p : A))
local notation "Bd" => derivedComplexCompletionFunctor Raw (c d)
local notation "Res" => derivedRestrictScalars c

/-- 概要：元のraw係数対象は、raw環自身のsingleを実係数射で制限した対象。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def monicPrismaticRawCoefficientRestrictionIso :
    (MonicPrismaticSourceRawCoefficientObject D d f).obj ≅ (Res).obj M :=
  DerivedCategory.Minus.ι.mapIso (monicPrismaticSourceRawCoefficientSingleIso D d f) ≪≫
    (algebraRestrictionSingleIso A Raw).symm

/-- 概要：raw環自身の二つの主元についての実逐次完備化。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
abbrev MonicPrismaticRawInternalIteratedCompletion := (Bd).obj ((Bp).obj M)

/-- 概要：二度のG8を同じ係数射に適用した、元のraw実逐次対象との同型。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def monicPrismaticRawIteratedRestrictionIso :
    (MonicPrismaticSourceRawIteratedCompletion D d f).obj ≅
      (Res).obj (MonicPrismaticRawInternalIteratedCompletion D d f) :=
  (Cd).mapIso ((Cp).mapIso (monicPrismaticRawCoefficientRestrictionIso D d f)) ≪≫
    (Cd).mapIso ((derivedCompletionRestrictionIso c (p : A)).app M) ≪≫
    (derivedCompletionRestrictionIso c d).app ((Bp).obj M)

/-- 概要：係数比較は両方の元の主元完備化単位を保つ。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
theorem monicPrismaticRawIteratedRestrictionIso_unit :
    ((derivedComplexCompletionUnit A (p : A)).app
        (MonicPrismaticSourceRawCoefficientObject D d f).obj ≫
      (derivedComplexCompletionUnit A d).app
        ((Cp).obj (MonicPrismaticSourceRawCoefficientObject D d f).obj)) ≫
      (monicPrismaticRawIteratedRestrictionIso D d f).hom =
    (monicPrismaticRawCoefficientRestrictionIso D d f).hom ≫
      (Res).map ((derivedComplexCompletionUnit Raw (c (p : A))).app M ≫
        (derivedComplexCompletionUnit Raw (c d)).app ((Bp).obj M)) := by
  let e := monicPrismaticRawCoefficientRestrictionIso D d f
  let eP := (Cp).mapIso e ≪≫ (derivedCompletionRestrictionIso c (p : A)).app M
  have hp : (derivedComplexCompletionUnit A (p : A)).app
      (MonicPrismaticSourceRawCoefficientObject D d f).obj ≫ eP.hom =
      e.hom ≫ (Res).map ((derivedComplexCompletionUnit Raw (c (p : A))).app M) := by
    have hn := (derivedComplexCompletionUnit A (p : A)).naturality e.hom
    simp only [Functor.id_map] at hn
    dsimp only [eP, Iso.trans_hom, Functor.mapIso_hom]
    rw [← Category.assoc, ← hn, Category.assoc]
    erw [derivedCompletionRestrictionIso_unit]
  have hd := (derivedComplexCompletionUnit A d).naturality eP.hom
  simp only [Functor.id_map] at hd
  have he : (monicPrismaticRawIteratedRestrictionIso D d f).hom =
      (Cd).map eP.hom ≫ (derivedCompletionRestrictionIso c d).hom.app ((Bp).obj M) := by
    simp only [monicPrismaticRawIteratedRestrictionIso, eP, e, Iso.trans_hom,
      Functor.mapIso_hom, Functor.map_comp, Category.assoc]
    rfl
  rw [he]
  simp only [Category.assoc]
  rw [← Category.assoc ((derivedComplexCompletionUnit A d).app _) ((Cd).map eP.hom),
    ← hd]
  simp only [Category.assoc]
  erw [derivedCompletionRestrictionIso_unit]
  rw [← Category.assoc, hp, Category.assoc, ← Functor.map_comp]

/-- 概要：raw環上の同じ実逐次完備化のH0へ、元のA作用を保って比較する。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def monicPrismaticRawIteratedRestrictionH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (MonicPrismaticSourceRawIteratedCompletion D d f).obj ≅
      (ModuleCat.restrictScalars c).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Raw) 0).obj
          (MonicPrismaticRawInternalIteratedCompletion D d f)) :=
  (DerivedCategory.homologyFunctor (ModuleCat A) 0).mapIso
    (monicPrismaticRawIteratedRestrictionIso D d f) ≪≫
      (derivedRestrictScalarsHomologyIso c 0).app _

/-- 概要：元の実モニック族添加源のH0をraw環上の実逐次完備化のH0と同定する。
方針：一般の標準 augmentation と実係数制限・完備化比較を、同じ実対象へ適用する。
規約：元の係数射と作用を保持し、モニック性・正次数・有限性を使わない。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実 H⁰ と raw PD 環の比較。 -/
def monicPrismaticSourceInternalRawH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (MonicPrismaticSourceIteratedPDCompletion D d f).obj ≅
      (ModuleCat.restrictScalars c).obj
        ((DerivedCategory.homologyFunctor (ModuleCat Raw) 0).obj
          (MonicPrismaticRawInternalIteratedCompletion D d f)) :=
  monicPrismaticSourceRawIteratedH0Iso D d f ≪≫ monicPrismaticRawIteratedRestrictionH0Iso D d f

end SerrePositivity.BhattScholze.Andre

end MonicPrismaticRawCompletionRestriction

/-! ## モニック源の実 H⁰ と raw PD 完備化環の比較

## 概要

一般モニック f/d 源の実逐次 p,d 完備化の H⁰ は、raw f/d 包の実 PD 完備化 H⁰ と A 線形同型。
BS 著者版 Remark 7.15（著者版 p.62）の実源と環候補の比較。

## 方針

源の標準 augmentation の H⁰ 比較、G8 の係数制限比較、既存の一般二座標 H⁰ 反射比較を合成する。
原典の BS 著者版 Proposition 7.11 を使う証明とは異なる具体的係数射を保つ計算。

## 規約

モニック性・正次数・有限性はこの比較には不要。高次消滅は別に証明済みの純性から得る。

## 使われ方

完全 prism 上の有限族の実源の離散性から、raw PD 環の元の係数射の完全忠実平坦性へ移す。
-/

@[expose] public noncomputable section MonicPrismaticRawPDComparison

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
open SerrePositivity.DerivedCompletion
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A)
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun t : σ => monicRelation (f t) t)
local notation "Raw" => DeltaAdjoinDivision E (MvPolynomial.C d) r
local notation "c" => algebraMap A Raw
local notation "z" => c d
local notation "a" => c (p : A)
local notation "Z" => MonicPrismaticRawInternalIteratedCompletion D d f
local notation "H" => CategoryTheory.Functor.obj (DerivedCategory.homologyFunctor (ModuleCat Raw) 0)

/-- 概要：raw 包自身の逐次実完備化 H⁰ は、元の Raw 線形単位を保って PD 完備化 H⁰ と同型。
方針：一般二座標 H⁰ 反射の既存比較をそのまま適用する。
規約：第一座標の像が自然数 p であることを明示する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の実源から環候補への比較の最終段。 -/
def monicPrismaticRawInternalPDLinearEquiv : H Z ≃ₗ[Raw] PDCompletionH0 Raw p z :=
  iteratedPDH0LinearEquiv Raw a z p (map_natCast c p)

/-- 概要：raw 自身の比較は、すべての raw 係数の元の標準完備化像を保つ。
方針：一般 H⁰ 反射比較の標準単位公式を再利用する。
規約：単位 1 だけでなく任意の raw 元で述べる。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の候補係数射との後続比較。 -/
theorem monicPrismaticRawInternalPDLinearEquiv_unit (x : Raw) :
    monicPrismaticRawInternalPDLinearEquiv D d f (iteratedPDH0Unit Raw a z x) =
      pairCompletionH0Unit Raw (p : Raw) z x :=
  iteratedPDH0LinearEquiv_unit Raw a z p (map_natCast c p) x

/-- 概要：元の実モニック源の逐次完備化 H⁰ は、raw PD 環の同じ A 係数制限と同型。
方針：標準 augmentation、二度の G8、Raw 線形 H⁰ 反射比較を順に合成する。
規約：元の A 作用を保つ加群同型を構成する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の環候補の完全忠実平坦性への移送。 -/
def monicPrismaticSourcePDH0Iso :
    (DerivedCategory.homologyFunctor (ModuleCat A) 0).obj
        (MonicPrismaticSourceIteratedPDCompletion D d f).obj ≅
      (ModuleCat.restrictScalars c).obj (ModuleCat.of Raw (PDCompletionH0 Raw p z)) :=
  monicPrismaticSourceInternalRawH0Iso D d f ≪≫
    (ModuleCat.restrictScalars c).mapIso
      (monicPrismaticRawInternalPDLinearEquiv D d f).toModuleIso

end SerrePositivity.BhattScholze.Andre

end MonicPrismaticRawPDComparison

/-! ## モニック源の実生成元冪商の G9 入力

## 概要

有限正次数モニック族の実逐次完備化の A/(p,dⁿ) 還元は離散かつ H⁰ が平坦であり、
A/(dⁿ) 還元は p 導来完備で標準 mod p 還元が離散かつ平坦。
BS 著者版 Remark 7.15（著者版 p.62）の生成元冪商計算。

## 方針

同じ実対象の標準冪零還元に G10 を適用し、一般商比較と G8 の完備性を接続する。
原典の BS 著者版 Proposition 7.11 を使う証明とは異なる経路の計算。

## 規約

正の冪と元の係数射に沿う実還元を使い、d mod p の正則性は要求しない。

## 使われ方

生成元冪商に G9 を適用し、完備化源の離散性と平坦性を導く。
-/

@[expose] public noncomputable section MonicPrismaticSourcePowerInputs

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (d : A) (f : σ → Polynomial A) (n : ℕ) (hn : 0 < n)
variable (hf : ∀ t, (f t).Monic) (hdeg : ∀ t, 0 < (f t).natDegree)
variable {m : ℕ} (s : Fin m ≃ σ)
variable (hpA : Function.Injective (fun x : A => (p : A) * x))
  (hd : IsSMulRegular A d) (v : Aˣ) (hv : (v : A) = D.delta d)
local notation "Qₙ" => A ⧸ Ideal.span {(p : A), d ^ n}
local notation "Kₙ" => prismaticPowerResidueIdeal (p : A) d n
local notation "X₀" => MonicPrismaticSourceIteratedPDCompletion D d f
local notation "Y₀" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : A), d ^ n}))) X₀
local notation "Tₙ" => A ⧸ Ideal.span {d ^ n}
local notation "Mₙ" => Tₙ ⧸ Ideal.span {(p : Tₙ)}
local notation "Zₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {d ^ n}))) X₀
local notation "Wₙ" => CategoryTheory.Functor.obj
  (boundedAboveDerivedBaseChange (Ideal.Quotient.mk (Ideal.span {(p : Tₙ)}))) Zₙ
include hn hf hdeg s hpA hd v hv

/-- 概要：G10により、実A/(p,dⁿ)還元は次数零に集中しH0が平坦。
方針：標準冪零還元の離散・忠実平坦性から G10 を適用し、実合成商比較で標準 mod p 商へ移す。
規約：正の冪 n、有限正次数モニック族、p と d の個別の正則性、δ(d) の単元性を仮定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の生成元冪商への G9 適用の入力。 -/
theorem monicPrismaticSourcePowerResidue_pure_flat :
    (Y₀).obj.IsGE 0 ∧ (Y₀).obj.IsLE 0 ∧
      Module.Flat Qₙ ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) 0).obj (Y₀).obj) := by
  have hPure := monicPrismaticSourceCanonicalPowerResidue_homology_isZero
    D d f n hn s hf hpA hd v hv
  have hFF := monicPrismaticSourceCanonicalPowerResidueH0_faithfullyFlat
    D d f n hn s hf hdeg hpA hd v hv
  let := hFF
  exact derived_pure_flat_of_nilpotent_reduction Kₙ Y₀ hPure
    inferInstance ⟨n, prismaticPowerResidueIdeal_pow (p : A) d n⟩

/-- 概要：G10で得た実冪剰余の非零次数ホモロジー消滅。
方針：標準冪零還元の離散・忠実平坦性から G10 を適用し、実合成商比較で標準 mod p 商へ移す。
規約：正の冪 n、有限正次数モニック族、p と d の個別の正則性、δ(d) の単元性を仮定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の生成元冪商への G9 適用の入力。 -/
theorem monicPrismaticSourcePowerResidue_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) i).obj (Y₀).obj) := by
  obtain ⟨hGE, hLE, _⟩ :=
    monicPrismaticSourcePowerResidue_pure_flat D d f n hn hf hdeg s hpA hd v hv
  rcases lt_or_gt_of_ne hi with h | h
  · exact (DerivedCategory.isGE_iff _ _).mp hGE i h
  · exact (DerivedCategory.isLE_iff _ _).mp hLE i h

/-- 概要：同じ実冪剰余のH0平坦性。
方針：標準冪零還元の離散・忠実平坦性から G10 を適用し、実合成商比較で標準 mod p 商へ移す。
規約：正の冪 n、有限正次数モニック族、p と d の個別の正則性、δ(d) の単元性を仮定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の生成元冪商への G9 適用の入力。 -/
theorem monicPrismaticSourcePowerResidueH0_flat :
    Module.Flat Qₙ ((DerivedCategory.homologyFunctor (ModuleCat Qₙ) 0).obj (Y₀).obj) :=
  (monicPrismaticSourcePowerResidue_pure_flat D d f n hn hf hdeg s hpA hd v hv).2.2

/-- 概要：A/(dⁿ)上の標準mod p実還元の非零次数ホモロジー消滅。
方針：標準冪零還元の離散・忠実平坦性から G10 を適用し、実合成商比較で標準 mod p 商へ移す。
規約：正の冪 n、有限正次数モニック族、p と d の個別の正則性、δ(d) の単元性を仮定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の生成元冪商への G9 適用の入力。 -/
theorem monicPrismaticSourceGeneratorPowerModP_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) i).obj (Wₙ).obj) :=
  prismaticGeneratorPowerModP_homology_isZero p d n X₀ i
    (monicPrismaticSourcePowerResidue_homology_isZero D d f n hn hf hdeg s hpA hd v hv i hi)

/-- 概要：標準mod p実還元のH0は、その正確な商環上で平坦。
方針：標準冪零還元の離散・忠実平坦性から G10 を適用し、実合成商比較で標準 mod p 商へ移す。
規約：正の冪 n、有限正次数モニック族、p と d の個別の正則性、δ(d) の単元性を仮定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の生成元冪商への G9 適用の入力。 -/
theorem monicPrismaticSourceGeneratorPowerModPH0_flat :
    Module.Flat Mₙ ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) 0).obj (Wₙ).obj) :=
  prismaticGeneratorPowerModPH0_flat p d n X₀
    (monicPrismaticSourcePowerResidueH0_flat D d f n hn hf hdeg s hpA hd v hv)

/-- 概要：G8の商上完備性とG10の実mod p入力を、G9用の同じ対象で束ねる。
方針：標準冪零還元の離散・忠実平坦性から G10 を適用し、実合成商比較で標準 mod p 商へ移す。
規約：正の冪 n、有限正次数モニック族、p と d の個別の正則性、δ(d) の単元性を仮定する。
使われ方：BS 著者版 Remark 7.15（著者版 p.62）の生成元冪商への G9 適用の入力。 -/
theorem monicPrismaticSourceGeneratorPower_G9_inputs :
    DerivedCompletion.IsComplete Tₙ (p : Tₙ) (Zₙ).obj ∧
      (∀ i : ℤ, i ≠ 0 →
        IsZero ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) i).obj (Wₙ).obj)) ∧
      Module.Flat Mₙ ((DerivedCategory.homologyFunctor (ModuleCat Mₙ) 0).obj (Wₙ).obj) := by
  exact ⟨monicPrismaticSourceGeneratorPowerReduction_isComplete_over_quotient D d f hd n,
    monicPrismaticSourceGeneratorPowerModP_homology_isZero D d f n hn hf hdeg s hpA hd v hv,
    monicPrismaticSourceGeneratorPowerModPH0_flat D d f n hn hf hdeg s hpA hd v hv⟩

end SerrePositivity.BhattScholze.Andre

end MonicPrismaticSourcePowerInputs
