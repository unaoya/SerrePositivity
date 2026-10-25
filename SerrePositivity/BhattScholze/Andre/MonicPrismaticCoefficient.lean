module

public import SerrePositivity.BhattScholze.Andre.MonicFamilyCoefficientQuotient
public import SerrePositivity.BhattScholze.Andre.RootedExtension.Division.DeltaDivisionFirstCoefficientPowerEquiv

/-!
# André E1・E2：一般 f/d 包の初期係数商

## 概要

任意正次数モニック族の f/d 包の初期係数商は、元の A/(p,d) 上忠実平坦。
BS Rem 7.15（著者版 p.62）の一般除算包の剰余計算の係数部分。

## 方針

実イデアルを (p,d) の係数拡張とモニック関係イデアルの和に分け、通常の全族商との
具体的同型で忠実平坦性を移す。原典の Prop 7.11 を使う経路とは異なる計算。

## 規約

δ 構造も係数環の正則性も不要。導来基底変更や完備化後の平坦性は主張しない。

## 使われ方

一般 f/d 包の raw (p,d) 剰余を元の係数環上へ戻す。
-/

@[expose] public noncomputable section

universe u

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
使われ方：BS Cor 2.39（著者版 p.25）の実 mod (p,d) 表示の係数環。 -/
abbrev MonicPrismaticCoefficientQuotient := P ⧸ J

/-- 概要：初期係数イデアルは (p,d) の係数拡張と関係多項式のイデアルの和。
方針：係数イデアルの拡張とモニック関係イデアルの定義を展開する。
規約：任意多項式族に成立する。
使われ方：BS Cor 2.39（著者版 p.25）の係数商を通常モニック商へ移す。 -/
theorem monicPrismaticCoefficientIdeal_eq :
    J = (I).map (MvPolynomial.C : A →+* P) ⊔ polynomialFamilyRelationIdeal f := by
  simp only [Ideal.map_span, Set.image_pair, map_natCast,
    deltaDivisionFirstBaseIdeal, polynomialFamilyRelationIdeal]

/-- 概要：f/d 包の初期係数商は mod (p,d) の多項式の通常商に同型。
方針：初期イデアルの表示と全族の係数商の交換同型を合成する。
規約：この同型は任意族に対して定義する。
使われ方：BS Rem 7.15（著者版 p.62）の実剰余の通常忠実平坦性。 -/
def monicPrismaticCoefficientEquiv : MonicPrismaticCoefficientQuotient p d f ≃+* C :=
  (Ideal.quotEquivOfEq (monicPrismaticCoefficientIdeal_eq p d f)).trans
    (polynomialFamilyBaseQuotientEquiv I (f))

/-- 概要：係数商同型は多項式の係数を mod (p,d) に写す。
方針：商イデアル同定と係数商同型の代表元公式を使う。
規約：元の変数は保持する。
使われ方：BS Cor 2.39（著者版 p.25）の実係数作用の比較。 -/
theorem monicPrismaticCoefficientEquiv_mk (x : P) :
    monicPrismaticCoefficientEquiv p d f (Ideal.Quotient.mk J x) =
      Ideal.Quotient.mk (polynomialFamilyRelationIdeal g) (MvPolynomial.map q x) := by
  rw [monicPrismaticCoefficientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    polynomialFamilyBaseQuotientEquiv_mk]

/-- 概要：表示同型は元の係数の標準像を A/(p,d) の通常係数作用に対応させる。
方針：代表元公式に定数多項式を代入する。
規約：元の A の任意元で述べる。
使われ方：BS Rem 7.15（著者版 p.62）の元の係数環への平坦性移送。 -/
theorem monicPrismaticCoefficientEquiv_C (x : A) :
    monicPrismaticCoefficientEquiv p d f (Ideal.Quotient.mk J (MvPolynomial.C x)) =
      algebraMap QA C (q x) := by
  rw [monicPrismaticCoefficientEquiv_mk, MvPolynomial.map_C]
  rfl

/-- 概要：初期係数商への標準 A/(p,d) 係数射。
方針：通常商への係数射を表示同型の逆で戻す。
規約：次の代表元公式で自然な係数射に一致することを確認する。
使われ方：BS Cor 2.39（著者版 p.25）の実係数商の代数構造。 -/
def monicPrismaticCoefficientBaseMap : QA →+* MonicPrismaticCoefficientQuotient p d f :=
  (monicPrismaticCoefficientEquiv p d f).symm.toRingHom.comp (algebraMap QA C)

/-- 概要：標準 A/(p,d) 係数射は元の A 係数の自然な商像で与えられる。
方針：表示同型を適用して元の係数像を比較する。
規約：環射の定義だけでなく代表元での等式を保証する。
使われ方：BS Rem 7.15（著者版 p.62）の raw 商の係数作用。 -/
theorem monicPrismaticCoefficientBaseMap_mk (x : A) :
    monicPrismaticCoefficientBaseMap p d f (q x) = Ideal.Quotient.mk J (MvPolynomial.C x) := by
  apply (monicPrismaticCoefficientEquiv p d f).injective
  change (monicPrismaticCoefficientEquiv p d f)
    ((monicPrismaticCoefficientEquiv p d f).symm _) = _
  rw [RingEquiv.apply_symm_apply, monicPrismaticCoefficientEquiv_C]

/-- 概要：標準係数射による初期係数商の A/(p,d) 代数構造。
方針：明示した環射の toAlgebra を用いる。
規約：利用箇所で局所的に導入する。
使われ方：BS Cor 2.39（著者版 p.25）の係数商の忠実平坦性。 -/
@[instance_reducible] def monicPrismaticCoefficientBaseAlgebra :
    Algebra QA (MonicPrismaticCoefficientQuotient p d f) :=
  (monicPrismaticCoefficientBaseMap p d f).toAlgebra

/-- 概要：初期係数商の表示は標準 A/(p,d) 係数作用に関する代数同型。
方針：表示同型の逆で定義した係数射との可換性を使う。
規約：元の A/(p,d) スカラーを変えない。
使われ方：BS Rem 7.15（著者版 p.62）の忠実平坦性の移送。 -/
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
使われ方：BS Rem 7.15(1)（著者版 p.62）の raw 実 mod (p,d) 商の忠実平坦性の係数入力。 -/
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
