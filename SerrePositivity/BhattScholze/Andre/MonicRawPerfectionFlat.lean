module

public import SerrePositivity.BhattScholze.Andre.MonicRawDerivedReduction
public import SerrePositivity.BhattScholze.DeltaAlgebraPerfectionResidue

/-!
# André E1・E2：補助 raw 包の δ 完全化の忠実平坦剰余

## 概要

完全 δ 係数環上で、正次数モニック族の補助 φ(f)/p 包の δ 完全化は p 完全忠実平坦。
BS Cor 2.39（著者版 p.25）、Rem 7.15（p.62）の準備。

## 方針

実 raw 包の導来 mod p 入力を、既存の一般 δ 完全化の剰余忠実平坦性に渡す。
完全化の p 正則性と主元判定を接続する。原典の Prop 7.11 とは異なる経路。

## 規約

δ 完全化は Frobenius の逐次余極限で、p 進完備化や一般 f/d 包との比較を含まない。
係数射は raw 包への射と完全化の第零段射の合成で固定する。

## 使われ方

補助包の p 進完備化と、最終 prismatic envelope の比較への検証済み入力。
-/

@[expose] public noncomputable section
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace SerrePositivity.BhattScholze.Andre
open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
attribute [local instance] HasDerivedCategory.standard
variable {p : ℕ} [Fact p.Prime] {A σ : Type u} [CommRing A]
variable (D : DeltaStructure p A) (f : σ → Polynomial A)
local notation "P" => MvPolynomial σ A
local notation "E" => polynomialRankOneDeltaStructure σ D
local notation "a" => (fun s : σ => DeltaStructure.frobeniusLift E (monicRelation (f s) s))
local notation "F" => deltaAdjoinDivisionStructure E (p : P) a
local notation "j" => monicRawCoefficientMap D f
local notation "C" => DeltaPerfection F
local notation "I" => Ideal.span {(p : A)}
local notation "QA" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I

/-- 概要：元の係数環から raw 包への係数射は δ 射。
方針：独立変数の δ 構造の係数包含と δ 除算射を合成する。
規約：φ(f)/p の任意関係族を使う。
使われ方：BS Rem 7.15（著者版 p.62）の完全化の自然性の入力。 -/
theorem monicRawCoefficient_isDeltaHom : D.IsDeltaHom F j :=
  (deltaAdjoinDivisionMap_isDeltaHom E (p : P) a).comp
    (polynomialRankOneDeltaStructure_C_isDeltaHom σ D)

/-- 概要：補助 raw 包の δ 完全化への実係数射。
方針：既存完全化の第零段射と raw 係数射を合成する。
規約：元の A 作用を明示する。
使われ方：BS Cor 2.39（著者版 p.25）の完全忠実平坦性を定式化する。 -/
def monicRawPerfectionCoefficientMap : A →+* C := deltaAlgebraPerfectionCoefficient F j

/-- 概要：δ 完全化の元の係数射による A 代数構造。
方針：明示的な実係数射から定める。
規約：使用箇所で局所導入する。
使われ方：BS Rem 7.15（著者版 p.62）の剰余テンソルの係数を固定する。 -/
@[instance_reducible] def monicRawPerfectionAlgebra : Algebra A C :=
  (monicRawPerfectionCoefficientMap D f).toAlgebra

attribute [local instance] monicRawPerfectionAlgebra

/-- 概要：完全係数環の任意正次数モニック族の δ 完全化の実剰余スカラー拡大は忠実平坦。
方針：raw 包の導来 mod p 入力を一般 δ 完全化の定理に適用する。
規約：一般定理の第二生成元は零とし、元の p 商へ同定する。
使われ方：BS Rem 7.15（著者版 p.62）の補助完全化の忠実性。 -/
theorem monicRawPerfection_scalarResidue_faithfullyFlat
    (hD : D.IsPerfect) (hf : ∀ s, (f s).Monic)
    (hdeg : ∀ s, 0 < (f s).natDegree) (hdp : D.IsDistinguished (p : A)) :
    Module.FaithfullyFlat QA ((ModuleCat.extendScalars q).obj
      (baseChangeScalarModule (monicRawPerfectionCoefficientMap D f))) := by
  have hz := monicRaw_modP_homology_isZero D f hD.p_mul_injective hf hdp
  have hFF := monicRaw_modPH0_faithfullyFlat D f hD.p_mul_injective hf hdp hdeg
  have h := deltaAlgebraPerfectionResidueTensor_faithfullyFlat D F j 0 hD
    (monicRawCoefficient_isDeltaHom D f)
    (by rw [Ideal.span_pair_zero]; exact hz) (by rw [Ideal.span_pair_zero]; exact hFF)
  rw [Ideal.span_pair_zero] at h
  exact h

/-- 概要：完全化の制限加群の剰余スカラー拡大は標準 A/p テンソルと線形同型。
方針：二つの標準商比較を合成する。
規約：完全化に明示した同じ係数作用を使用する。
使われ方：BS Cor 2.39（著者版 p.25）の主元判定への入力。 -/
def monicRawPerfection_scalarResidueTensorEquiv :
    ((ModuleCat.extendScalars q).obj
      (baseChangeScalarModule (monicRawPerfectionCoefficientMap D f))) ≃ₗ[QA] QA ⊗[A] C := by
  let M := baseChangeScalarModule (monicRawPerfectionCoefficientMap D f)
  let e : M ≃ₗ[A] C :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  exact (quotientScalarExtensionEquiv I M).trans
    (((quotientModuleFunctor I).mapIso e.toModuleIso).toLinearEquiv.trans
      (quotientTensorReductionEquiv I C).symm)

/-- 概要：δ 完全化の元の係数作用の通常剰余テンソルは忠実平坦。
方針：実剰余スカラー拡大との標準線形同型で移す。
規約：完全 δ 係数環、任意正次数モニック族、δ(p) の単元性を要求する。
使われ方：BS Cor 2.39（著者版 p.25）の主元判定。 -/
theorem monicRawPerfection_residueTensor_faithfullyFlat
    (hD : D.IsPerfect) (hf : ∀ s, (f s).Monic)
    (hdeg : ∀ s, 0 < (f s).natDegree) (hdp : D.IsDistinguished (p : A)) :
    Module.FaithfullyFlat QA (QA ⊗[A] C) := by
  have := monicRawPerfection_scalarResidue_faithfullyFlat D f hD hf hdeg hdp
  exact Module.FaithfullyFlat.of_linearEquiv QA _
    (monicRawPerfection_scalarResidueTensorEquiv D f).symm

/-- 概要：δ 完全化で元の係数環の p スカラーは正則。
方針：完全 δ 環の p 正則性と係数射の自然数保存を使う。
規約：この正則性自体にはモニック性も基底の完全性も不要。
使われ方：BS Cor 2.39（著者版 p.25）の主元判定の Tor 入力。 -/
theorem monicRawPerfection_p_smul_regular : IsSMulRegular C (p : A) := by
  intro x y h
  apply (deltaPerfection_isPerfect F).p_mul_injective
  simpa only [Algebra.smul_def, map_natCast] using h

/-- 概要：完全係数環上の任意正次数モニック族の補助 δ 完全化は p 完全忠実平坦。
方針：通常剰余テンソルの忠実平坦性と p 正則性を主元判定に渡す。
規約：p 進完備化前の Frobenius 余極限である。
使われ方：BS Rem 7.15（著者版 p.62）の補助包と最終 envelope の比較への準備。 -/
theorem monicRawPerfection_isCompletelyFaithfullyFlat
    (hD : D.IsPerfect) (hf : ∀ s, (f s).Monic)
    (hdeg : ∀ s, 0 < (f s).natDegree) (hdp : D.IsDistinguished (p : A)) :
    IsCompletelyFaithfullyFlat I C :=
  isCompletelyFaithfullyFlat_principal_of_regular (p : A) hD.p_mul_injective C
    (monicRawPerfection_p_smul_regular D f)
    (monicRawPerfection_residueTensor_faithfullyFlat D f hD hf hdeg hdp)

end SerrePositivity.BhattScholze.Andre
