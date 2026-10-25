module

public import SerrePositivity.BhattScholze.Andre.Variants.MonicRawModPFlat
public import SerrePositivity.BhattScholze.Andre.Variants.MonicFamilyRawRegular
public import SerrePositivity.BhattScholze.Semiperfectoid.RootedExtension.DeltaRoot.DeltaRootSourceRegularGhost
public import SerrePositivity.CommutativeAlgebra.CompletelyFlatCriterion
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# André E1・E2：任意モニック族の補助 raw φ/p 包の p 完全忠実平坦性

## 概要

p 正則な δ 係数環上で δ(p) が単元なら、正次数モニック族の補助 raw φ/p 包は
元の係数射に関して p 完全忠実平坦。BS 著者版 Cor 2.39（p.25）、Rem 7.15（p.62）の準備。

## 方針

実 p 商の忠実平坦性を元の A→A/p に沿う通常テンソルの忠実平坦性へ移す。
前工程の raw p 正則性と主元の完全忠実平坦性判定を組み合わせる。

## 規約

これは補助 φ(f)/p 包の結果であり、f/d 包やその perfectoid 商の平坦性ではない。
族の有限性や ghost 単射を追加仮定にしない。p 正則性は基底 prism の台環に要求する。

## 使われ方

prismatic envelope の比較で必要となる補助 pd 計算の p 完全忠実平坦性を供給する。
-/

@[expose] public noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace SerrePositivity.BhattScholze.Andre

open scoped TensorProduct

variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (f : σ → Polynomial A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "a" => (fun s : σ => DeltaStructure.frobeniusLift E (monicRelation (f s) s))
local notation "B" => DeltaAdjoinDivision E (p : P) a
local notation "I" => Ideal.span {(p : A)}
local notation "QA" => A ⧸ I

/-- 概要：元の δ 係数環から補助 raw 包への実係数射。
方針：多項式係数包含と raw δ 添加の係数射を合成する。
規約：標準の A 代数作用と同じ射を用いる。
使われ方：BS Cor 2.39（著者版 p.25）の元の係数作用を明示する。 -/
def monicRawCoefficientMap : A →+* B :=
  (deltaAdjoinDivisionMap E (p : P) a).comp MvPolynomial.C

/-- 概要：raw 包の標準代数構造の係数射は明示した実係数射と一致する。
方針：定義の一致による。
規約：係数作用を別の代数構造に取り替えない。
使われ方：BS Rem 7.15（著者版 p.62）の剰余テンソルの係数比較。 -/
theorem monicRawCoefficient_algebraMap : algebraMap A B = monicRawCoefficientMap D f := rfl

/-- 概要：基底の p イデアルの raw 包への拡張は raw 包自身の p イデアル。
方針：環射の自然数係数の保存を使う。
規約：元の A 係数射に沿う拡張。
使われ方：BS Cor 2.39（著者版 p.25）の通常 mod p 基底変更を同定する。 -/
theorem monicRawCoefficient_map_span_p :
    (I).map (algebraMap A B) = Ideal.span {(p : B)} := by
  simp only [Ideal.map_span, Set.image_singleton, map_natCast]

variable (hpA : Function.Injective (fun x : A => (p : A) * x))
variable (hg : Function.Injective (WittVector.ghostMap :
  WittVector p (RelativeFreeDeltaRing (R := MvPolynomial σ A) σ) →
    ℕ → RelativeFreeDeltaRing (R := MvPolynomial σ A) σ))
variable (w : Aˣ) (hw : (w : A) = D.delta (p : A))

/-- 概要：基底の p イデアルの拡張による商と実 raw p 商の比較は A/p 代数同型。
方針：拡張イデアルの等式と、係数の代表元公式を使う。
規約：実 p 商には前工程の明示的な A/p 作用を用いる。
使われ方：BS Rem 7.15（著者版 p.62）の元の係数剰余作用を保持する。 -/
def monicRawCoefficientQuotientAlgEquiv :
    letI := monicRawModPBaseAlgebra D f hpA hg w hw
    (B ⧸ (I).map (algebraMap A B)) ≃ₐ[QA] (B ⧸ Ideal.span {(p : B)}) := by
  let := monicRawModPBaseAlgebra D f hpA hg w hw
  apply AlgEquiv.ofRingEquiv (f := Ideal.quotEquivOfEq (monicRawCoefficient_map_span_p D f))
  intro x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  change Ideal.quotEquivOfEq (monicRawCoefficient_map_span_p D f)
    (Ideal.Quotient.mk _ (monicRawCoefficientMap D f x)) =
      monicRawModPBaseMap D f hpA hg w hw (Ideal.Quotient.mk I x)
  rw [Ideal.quotEquivOfEq_mk, monicRawModPBaseMap_mk]
  rfl

/-- 概要：元の A→A/p に沿う通常基底変更は実 raw p 商に A/p 代数同型。
方針：商テンソル比較と実 p 商の係数作用の同型を合成する。
規約：元の標準 A 代数作用を固定する。
使われ方：BS Cor 2.39（著者版 p.25）の主元平坦性判定の剰余テンソル。 -/
def monicRawBaseChangeModPAlgEquiv :
    letI := monicRawModPBaseAlgebra D f hpA hg w hw
    QA ⊗[A] B ≃ₐ[QA] (B ⧸ Ideal.span {(p : B)}) := by
  let := monicRawModPBaseAlgebra D f hpA hg w hw
  exact (Algebra.TensorProduct.quotIdealMapEquivQuotTensor B I).symm.trans
    (monicRawCoefficientQuotientAlgEquiv D f hpA hg w hw)

include hpA w hw in
omit hg in
/-- 概要：正次数モニック族の raw 包の通常剰余テンソルは A/p 上忠実平坦。
方針：G4 で ghost 単射を供給し、実 p 商との代数同型で忠実平坦性を移す。
規約：族の濃度に制限せず、外部 ghost 仮定を要求しない。
使われ方：BS Rem 7.15（著者版 p.62）の p 完全忠実平坦性の剰余入力。 -/
theorem monicRaw_residueTensor_faithfullyFlat
    (hf : ∀ s, (f s).Monic) (hdeg : ∀ s, 0 < (f s).natDegree) :
    Module.FaithfullyFlat QA (QA ⊗[A] B) := by
  let hg := deltaRootSource_ghostMap_injective (σ := σ) hpA
  let := monicRawModPBaseAlgebra D f hpA hg w hw
  let := monicRawModP_faithfullyFlat D f hpA hg w hw hf hdeg
  exact Module.FaithfullyFlat.of_linearEquiv QA (B ⧸ Ideal.span {(p : B)})
    (monicRawBaseChangeModPAlgEquiv D f hpA hg w hw).toLinearEquiv

include hpA in
omit hg w hw in
/-- 概要：raw 包の p 正則性を元の係数スカラー作用について表す。
方針：任意モニック族の raw p 正則性と自然数係数の保存を使う。
規約：モニック性は使うが正次数は不要。
使われ方：BS Cor 2.39（著者版 p.25）の主元平坦性判定の Tor 消滅入力。 -/
theorem monicRaw_p_smul_regular (hf : ∀ s, (f s).Monic)
    (hdp : D.IsDistinguished (p : A)) : IsSMulRegular B (p : A) := by
  intro x y hxy
  apply monicFamilyRaw_p_mul_injective D f hf hpA hdp
  simpa only [Algebra.smul_def, map_natCast] using hxy

include hpA in
omit hg w hw in
/-- 概要：任意正次数モニック族の補助 raw φ/p 包は元の係数射で p 完全忠実平坦。
方針：係数と raw 包の p 正則性、実剰余テンソルの忠実平坦性を主元の判定へ渡す。
規約：δ(p) の単元性を明示し、完備化後の主張と区別する。
使われ方：BS Rem 7.15（著者版 p.62）の一般 prism 包との比較への補助入力。 -/
theorem monicFamilyRaw_isCompletelyFaithfullyFlat
    (hf : ∀ s, (f s).Monic) (hdeg : ∀ s, 0 < (f s).natDegree)
    (hdp : D.IsDistinguished (p : A)) : IsCompletelyFaithfullyFlat I B := by
  have hB := monicRaw_p_smul_regular D f hpA hf hdp
  obtain ⟨w, hw⟩ := hdp
  exact isCompletelyFaithfullyFlat_principal_of_regular (p : A) hpA B hB
    (monicRaw_residueTensor_faithfullyFlat D f hpA w hw hf hdeg)

omit D hpA hg w hw in
/-- 概要：完全 prism 上の任意正次数モニック族の補助 raw φ/p 包は p 完全忠実平坦。
方針：完全 δ 構造の p 正則性と p 完備性から前定理の入力を内部で供給する。
規約：最終 f/d 包やその perfectoid 商の忠実平坦性はまだ主張しない。
使われ方：BS Rem 7.15（著者版 p.62）の完全 prism の補助 pd 計算。 -/
theorem perfectPrismMonicFamilyRaw_isCompletelyFaithfullyFlat
    (P₀ : OrientedPrism p A) (hP : P₀.deltaStructure.IsPerfect)
    (hf : ∀ s, (f s).Monic) (hdeg : ∀ s, 0 < (f s).natDegree) :
    IsCompletelyFaithfullyFlat (Ideal.span {(p : A)})
      (DeltaAdjoinDivision (polynomialRankOneDeltaStructure σ P₀.deltaStructure)
        (p : MvPolynomial σ A)
        (fun s : σ => DeltaStructure.frobeniusLift
          (polynomialRankOneDeltaStructure σ P₀.deltaStructure) (monicRelation (f s) s))) := by
  let := P₀.isAdicComplete_p_of_perfect hP
  apply monicFamilyRaw_isCompletelyFaithfullyFlat P₀.deltaStructure f hP.p_mul_injective hf hdeg
  exact DeltaStructure.isDistinguished_p P₀.deltaStructure
    (IsAdicComplete.le_jacobson_bot (Ideal.span {(p : A)}) (Ideal.mem_span_singleton_self _))

end SerrePositivity.BhattScholze.Andre
