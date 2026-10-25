module

public import SerrePositivity.BhattScholze.Andre.MonicFamilyCoefficientQuotient
public import SerrePositivity.BhattScholze.Andre.RootedExtension.Supplement.Division.DeltaPDivisionNextInput
public import SerrePositivity.BhattScholze.Delta.Free.PolynomialRankOneDelta

/-!
# André E1・E2：モニック族の raw Frobenius 除算の初期係数商

## 概要

任意のモニック族の raw φ/p 包の初期係数商を、mod p における関係の p 乗の通常商として表示する。
正次数モニック族ならこの係数商は A/p 上忠実平坦。
BS 著者版 Cor 2.39（p.25）、Rem 7.15(1)（p.62）の実剰余計算の一部である。

## 方針

一般 δ 除算の初期イデアルの Frobenius・冪比較と、全族の係数商の交換同型を合成する。
前工程の任意モニック族の通常忠実平坦性を標準係数射に沿って移す。

## 規約

同型自体にはモニック性・正次数・p 正則性を要求しない。
忠実平坦性にはモニック性と正次数を要求する。raw 包全体や完備化後の平坦性は別工程。

## 使われ方

一般 δ 除算の raw mod p 商の忠実平坦性を元の A/p に対して供給する。
-/

@[expose] public noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

namespace SerrePositivity.BhattScholze.Andre

variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (f : σ → Polynomial A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "r" => (fun s : σ => monicRelation (f s) s)
local notation "a" => (fun s : σ => DeltaStructure.frobeniusLift E (r s))
local notation "I" => Ideal.span {(p : A)}
local notation "QA" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "J" => deltaDivisionFirstBaseIdeal (p := p) (p : P) a
local notation "g" => (fun s : σ => Polynomial.map q (f s ^ p))
local notation "C" => PolynomialFamilyQuotient g

/-- 概要：モニック関係族の raw φ/p 包の初期係数商。
方針：既存 δ 除算の初期係数イデアルの商をそのまま使う。
規約：関係式のモニック性は定義に含めない。
使われ方：BS Cor 2.39（著者版 p.25）の実 mod p 表示の係数環。 -/
abbrev MonicFrobeniusCoefficientQuotient := P ⧸ J

/-- 概要：初期係数イデアルは p の係数拡張と関係多項式の p 乗のイデアルの和。
方針：Frobenius と p 乗の初期イデアル比較、および評価と冪の可換性を使う。
規約：任意多項式族に成立する。
使われ方：BS Cor 2.39（著者版 p.25）の係数商を通常モニック商へ移す。 -/
theorem monicFrobeniusCoefficientIdeal_eq :
    J = (I).map (MvPolynomial.C : A →+* P) ⊔ polynomialFamilyRelationIdeal (fun s => f s ^ p) := by
  rw [deltaPDivisionFirstBaseIdeal_frobenius_eq_power]
  unfold deltaDivisionFirstBaseIdeal
  have hpp : Ideal.span {(p : P), (p : P)} = Ideal.span {(p : P)} :=
    congrArg Ideal.span (Set.insert_eq_of_mem (Set.mem_singleton (p : P)))
  rw [hpp]
  simp only [Ideal.map_span, Set.image_singleton, map_natCast]
  congr 1
  unfold polynomialFamilyRelationIdeal
  congr 1
  congr 1
  funext s
  exact (Polynomial.eval₂_pow _ _ p).symm

/-- 概要：raw 初期係数商は mod p の多項式の p 乗の通常商に同型。
方針：初期イデアルの表示と全族の係数商の交換同型を合成する。
規約：この同型は任意族に対して定義する。
使われ方：BS Rem 7.15（著者版 p.62）の実剰余の通常忠実平坦性。 -/
def monicFrobeniusCoefficientEquiv : MonicFrobeniusCoefficientQuotient D f ≃+* C :=
  (Ideal.quotEquivOfEq (monicFrobeniusCoefficientIdeal_eq D f)).trans
    (polynomialFamilyBaseQuotientEquiv I (fun s => f s ^ p))

/-- 概要：係数商同型は多項式の係数を mod p に写す。
方針：商イデアル同定と係数商同型の代表元公式を使う。
規約：元の変数は保持する。
使われ方：BS Cor 2.39（著者版 p.25）の実係数作用の比較。 -/
theorem monicFrobeniusCoefficientEquiv_mk (x : P) :
    monicFrobeniusCoefficientEquiv D f (Ideal.Quotient.mk J x) =
      Ideal.Quotient.mk (polynomialFamilyRelationIdeal g) (MvPolynomial.map q x) := by
  rw [monicFrobeniusCoefficientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    polynomialFamilyBaseQuotientEquiv_mk]

/-- 概要：表示同型は元の係数の標準像を A/p の通常係数作用に対応させる。
方針：代表元公式に定数多項式を代入する。
規約：元の A の任意元で述べる。
使われ方：BS Rem 7.15（著者版 p.62）の元の係数環への平坦性移送。 -/
theorem monicFrobeniusCoefficientEquiv_C (x : A) :
    monicFrobeniusCoefficientEquiv D f (Ideal.Quotient.mk J (MvPolynomial.C x)) =
      algebraMap QA C (q x) := by
  rw [monicFrobeniusCoefficientEquiv_mk, MvPolynomial.map_C]
  rfl

/-- 概要：初期係数商への標準 A/p 係数射。
方針：通常商への係数射を表示同型の逆で戻す。
規約：次の代表元公式で自然な係数射に一致することを確認する。
使われ方：BS Cor 2.39（著者版 p.25）の実係数商の代数構造。 -/
def monicFrobeniusCoefficientBaseMap : QA →+* MonicFrobeniusCoefficientQuotient D f :=
  (monicFrobeniusCoefficientEquiv D f).symm.toRingHom.comp (algebraMap QA C)

/-- 概要：標準 A/p 係数射は元の A 係数の自然な商像で与えられる。
方針：表示同型を適用して元の係数像を比較する。
規約：環射の定義だけでなく代表元での等式を保証する。
使われ方：BS Rem 7.15（著者版 p.62）の raw 商の係数作用。 -/
theorem monicFrobeniusCoefficientBaseMap_mk (x : A) :
    monicFrobeniusCoefficientBaseMap D f (q x) = Ideal.Quotient.mk J (MvPolynomial.C x) := by
  apply (monicFrobeniusCoefficientEquiv D f).injective
  change (monicFrobeniusCoefficientEquiv D f)
    ((monicFrobeniusCoefficientEquiv D f).symm _) = _
  rw [RingEquiv.apply_symm_apply, monicFrobeniusCoefficientEquiv_C]

/-- 概要：標準係数射による初期係数商の A/p 代数構造。
方針：明示した環射の toAlgebra を用いる。
規約：利用箇所で局所的に導入する。
使われ方：BS Cor 2.39（著者版 p.25）の係数商の忠実平坦性。 -/
@[instance_reducible] def monicFrobeniusCoefficientBaseAlgebra :
    Algebra QA (MonicFrobeniusCoefficientQuotient D f) :=
  (monicFrobeniusCoefficientBaseMap D f).toAlgebra

/-- 概要：初期係数商の表示は標準 A/p 係数作用に関する代数同型。
方針：表示同型の逆で定義した係数射との可換性を使う。
規約：元の A/p スカラーを変えない。
使われ方：BS Rem 7.15（著者版 p.62）の忠実平坦性の移送。 -/
def monicFrobeniusCoefficientAlgEquiv :
    letI := monicFrobeniusCoefficientBaseAlgebra D f
    MonicFrobeniusCoefficientQuotient D f ≃ₐ[QA] C := by
  let := monicFrobeniusCoefficientBaseAlgebra D f
  apply AlgEquiv.ofRingEquiv (f := monicFrobeniusCoefficientEquiv D f)
  intro x
  exact (monicFrobeniusCoefficientEquiv D f).apply_symm_apply _

/-- 概要：正次数モニック族の raw 初期係数商は A/p 上忠実平坦。
方針：mod p の非零係数環ではモニック性と次数を保つ係数変更を使い、
通常の任意モニック族商の忠実平坦性を移す。零係数商は加群の自明性で処理する。
規約：A の p 正則性も族の有限性も不要。
使われ方：BS Rem 7.15(1)（著者版 p.62）の raw 実 mod p 商の忠実平坦性の係数入力。 -/
theorem monicFrobeniusCoefficient_faithfullyFlat
    (hf : ∀ s, (f s).Monic) (hdeg : ∀ s, 0 < (f s).natDegree) :
    letI := monicFrobeniusCoefficientBaseAlgebra D f
    Module.FaithfullyFlat QA (MonicFrobeniusCoefficientQuotient D f) := by
  let := monicFrobeniusCoefficientBaseAlgebra D f
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
        exact ((hf s).pow p).map q
      · intro s
        rw [((hf s).pow p).natDegree_map, (hf s).natDegree_pow]
        exact Nat.mul_pos (Fact.out : p.Prime).pos (hdeg s)
  let := hc
  exact Module.FaithfullyFlat.of_linearEquiv QA C
    (monicFrobeniusCoefficientAlgEquiv D f).toLinearEquiv

end SerrePositivity.BhattScholze.Andre
