module

public import SerrePositivity.BhattScholze.Andre.Variants.MonicRawCompletelyFlat
public import SerrePositivity.HomologicalAlgebra.DerivedBaseChangeDiscrete

/-!
# André E1・E2：補助 raw 包の実導来 p 剰余

## 概要

任意正次数モニック族の補助 φ(f)/p 包は、実導来 mod p 還元の非零次数が消え、
H⁰ が A/p 上忠実平坦である。BS Cor 2.39（著者版 p.25）、Rem 7.15（p.62）の準備。

## 方針

元の係数射の p 正則性から標準 augmentation を同型にし、実 H⁰ 比較で通常忠実平坦性を移す。

## 規約

対象は補助 raw 包の single の実導来還元である。一般 f/d 包との比較は主張しない。
原典の Prop 7.11 を使う証明とは異なる経路の補助計算。

## 使われ方

既存の一般 δ 完全化の剰余比較へ、明示した元の係数射に関する入力を渡す。
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
local notation "B" => DeltaAdjoinDivision E (p : P) a
local notation "j" => monicRawCoefficientMap D f
local notation "I" => Ideal.span {(p : A)}
local notation "QA" => A ⧸ I
local notation "q" => Ideal.Quotient.mk I
local notation "M" => baseChangeScalarModule j
local notation "Y" => CategoryTheory.Functor.obj (boundedAboveDerivedBaseChange q)
  (CategoryTheory.Functor.obj boundedAboveDerivedSingleFunctor M)
variable (hpA : Function.Injective (fun x : A => (p : A) * x))
variable (hf : ∀ s, (f s).Monic) (hdp : D.IsDistinguished (p : A))
include hpA hf hdp

/-- 概要：元の係数射の制限加群で p は正則。
方針：raw 包の標準 p 作用の正則性を係数射の定義で移す。
規約：モニック性と係数環の p 正則性、δ(p) の単元性を用いる。
使われ方：BS Cor 2.39（著者版 p.25）の実導来剰余の Tor 入力。 -/
theorem monicRaw_scalarModule_p_regular : IsSMulRegular M (p : A) := by
  intro x y h
  change B at x y
  apply monicFamilyRaw_p_mul_injective D f hf hpA hdp
  change j (p : A) * x = j (p : A) * y at h
  simpa only [map_natCast] using h

/-- 概要：補助 raw 包の元の係数射は、p 商に沿う高次 Tor が消える。
方針：係数環と制限加群の p 正則性に主元 Tor 判定を適用する。
規約：実係数加群を固定する。
使われ方：BS Rem 7.15（著者版 p.62）の実導来 mod p 還元を離散化する。 -/
theorem monicRaw_scalarExtensionTorVanishing : scalarExtensionTorVanishing q M :=
  scalarExtensionTorVanishing_principal_of_regular (p : A) hpA M
    (monicRaw_scalarModule_p_regular D f hpA hf hdp)

/-- 概要：raw 包の実導来 mod p 還元は通常剰余の single と標準同型。
方針：前定理を標準 augmentation の同型判定に渡す。
規約：導来対象の抽象的な置き換えではなく既存 augmentation を使う。
使われ方：BS Rem 7.15（著者版 p.62）の次数零比較への準備。 -/
def monicRaw_modPAugmentationIso :
    Y ≅ boundedAboveDerivedSingleFunctor.obj ((ModuleCat.extendScalars q).obj M) :=
  boundedAboveDerivedBaseChangeModuleAugmentationIso q M
    (monicRaw_scalarExtensionTorVanishing D f hpA hf hdp)

/-- 概要：補助 raw 包の実導来 mod p 還元の非零次数ホモロジーは零。
方針：標準 augmentation 同型から single のホモロジー消滅を移す。
規約：全非零整数次数を扱う。
使われ方：BS Rem 7.15（著者版 p.62）の δ 完全化の実剰余入力。 -/
theorem monicRaw_modP_homology_isZero (i : ℤ) (hi : i ≠ 0) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat QA) i).obj (Y).obj) := by
  let e := (DerivedCategory.homologyFunctor (ModuleCat QA) i).mapIso
    (DerivedCategory.Minus.ι.mapIso (monicRaw_modPAugmentationIso D f hpA hf hdp))
  exact (derivedSingleHomology_isZero ((ModuleCat.extendScalars q).obj M) i hi).of_iso e

omit hpA hf hdp in
/-- 概要：制限加群の通常 p 剰余と、標準 raw 係数作用の通常テンソルは A/p 線形同型。
方針：商スカラー拡大と商テンソルの二つの標準比較を合成する。
規約：係数射の定義による同じ A 作用を使う。
使われ方：BS Cor 2.39（著者版 p.25）の忠実平坦性を実 H⁰ に移す。 -/
def monicRaw_scalarResidueTensorEquiv :
    ((ModuleCat.extendScalars q).obj M) ≃ₗ[QA] QA ⊗[A] B := by
  let e : M ≃ₗ[A] B :=
    { toFun := fun x => x
      invFun := fun x => x
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl
      map_smul' := by
        intro c x
        change B at x
        simp only [RingHom.id_apply]
        rw [Algebra.smul_def]
        change j c * x = algebraMap A B c * x
        rw [monicRawCoefficient_algebraMap] }
  exact (quotientScalarExtensionEquiv I M).trans
    (((quotientModuleFunctor I).mapIso e.toModuleIso).toLinearEquiv.trans
      (quotientTensorReductionEquiv I B).symm)

/-- 概要：補助 raw 包の実導来 mod p 還元の H⁰ は A/p 上忠実平坦。
方針：通常剰余テンソルの忠実平坦性を実 H⁰ の標準線形同型で移す。
規約：任意濃度の正次数モニック族。ghost 単射仮定は内部で解消する。
使われ方：BS Rem 7.15（著者版 p.62）の一般 δ 完全化の剰余入力。 -/
theorem monicRaw_modPH0_faithfullyFlat (hdeg : ∀ s, 0 < (f s).natDegree) :
    Module.FaithfullyFlat QA
      ((DerivedCategory.homologyFunctor (ModuleCat QA) 0).obj (Y).obj) := by
  obtain ⟨w, hw⟩ := hdp
  have := monicRaw_residueTensor_faithfullyFlat D f hpA w hw hf hdeg
  let e := ((boundedAboveDerivedBaseChangeModuleH0Iso q).app M).toLinearEquiv |>.trans
    (monicRaw_scalarResidueTensorEquiv D f)
  exact Module.FaithfullyFlat.of_linearEquiv QA (QA ⊗[A] B) e

end SerrePositivity.BhattScholze.Andre
