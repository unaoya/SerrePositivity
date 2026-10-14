module

public import SerrePositivity.BhattScholze.OrientedPrismHomRigidity
public import Mathlib.LinearAlgebra.TensorProduct.Lift

/-! # 完全oriented prism射のイデアルのテンソル基底変換

著者公開版Lemma 3.5の主イデアルの場合。標準的なB⊗A Iの順序で
自然な乗法写像を構成し、それがB線形同型であると証明する。
一般Cartierイデアルへの忠実平坦降下は含めない。
-/

@[expose] public noncomputable section
open scoped TensorProduct
universe u v
namespace SerrePositivity.BhattScholze.OrientedPrism
variable {p : ℕ} [Fact p.Prime] {A : Type u} [CommRing A]

/-- 選択した非零因子の生成元によるprismイデアルの具体的な自明化。 -/
def generatorLinearEquiv (P : OrientedPrism p A) : A ≃ₗ[A] P.ideal :=
  LinearEquiv.ofBijective
    ((LinearMap.mulLeft A P.generator).codRestrict P.ideal
      (fun r ↦ P.ideal.mul_mem_right r (Ideal.subset_span (Set.mem_singleton _))))
    ⟨fun _ _ h ↦ P.generator_regular (congrArg Subtype.val h), by
      intro x
      obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp x.property
      exact ⟨r, Subtype.ext hr.symm⟩⟩

/-- prismイデアルの自明化は選択生成元の乗法。 -/
@[simp] theorem generatorLinearEquiv_apply (P : OrientedPrism p A) (r : A) :
    (P.generatorLinearEquiv r : A) = P.generator * r := rfl

namespace Hom
variable {B : Type v} [CommRing B]
variable {P : OrientedPrism p A} {Q : OrientedPrism p B}

section Compatible
variable [Algebra A B]

/-- prism射と両立するA代数構造に関して、イデアル上の標準A線形写像。 -/
def idealLinearMap (f : Hom P Q) (hf : f.toRingHom = algebraMap A B) : P.ideal →ₗ[A] Q.ideal where
  toFun x := ⟨f.toRingHom (x : A), f.ideal_le x.property⟩
  map_add' x y := Subtype.ext (map_add f.toRingHom (x : A) (y : A))
  map_smul' a x := by
    apply Subtype.ext
    simp [Algebra.smul_def, map_mul, hf]

/-- イデアルのテンソル基底変換の標準B線形写像。 -/
def idealTensorMap (f : Hom P Q) (hf : f.toRingHom = algebraMap A B) :
    B ⊗[A] P.ideal →ₗ[B] Q.ideal :=
  (f.idealLinearMap hf).liftBaseChange B

/-- 純テンソルの標準写像はb*f(x)。 -/
@[simp] theorem idealTensorMap_tmul (f : Hom P Q) (hf : f.toRingHom = algebraMap A B)
    (b : B) (x : P.ideal) :
    (f.idealTensorMap hf (b ⊗ₜ[A] x) : B) = b * f.toRingHom x := rfl

/-- 完全oriented prism間の標準イデアル基底変換写像は全単射。
正則生成元による自明化と、生成元の像の一意な単元係数から証明する。 -/
theorem idealTensorMap_bijective (f : Hom P Q) (hf : f.toRingHom = algebraMap A B)
    (hP : P.deltaStructure.IsPerfect) (hQ : Q.deltaStructure.IsPerfect) :
    Function.Bijective (f.idealTensorMap hf) := by
  obtain ⟨u, hu, _⟩ := f.existsUnique_generator_unit hP hQ
  let e₁ := (P.generatorLinearEquiv.symm.baseChange A B P.ideal A).trans
    (TensorProduct.AlgebraTensorModule.rid A B B)
  let e₂ := (LinearEquiv.smulOfUnit u : B ≃ₗ[B] B).trans Q.generatorLinearEquiv
  have he : f.idealTensorMap hf = (e₁.trans e₂).toLinearMap := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro b x
    apply Subtype.ext
    let r := P.generatorLinearEquiv.symm x
    have hx : (x : A) = P.generator * r := by
      have h := congrArg Subtype.val (P.generatorLinearEquiv.apply_symm_apply x)
      exact h.symm
    change b * f.toRingHom (x : A) = Q.generator * ((u : B) * (r • b))
    rw [hx, map_mul, hu, hf]
    rw [Algebra.smul_def]
    change b * (Q.generator * (u : B) * (algebraMap A B r)) =
      Q.generator * ((u : B) * (algebraMap A B r * b))
    ring
  rw [he]
  exact (e₁.trans e₂).bijective

/-- 標準イデアル基底変換写像そのものを台写像とする具体的なB線形同型。 -/
def idealTensorEquiv (f : Hom P Q) (hf : f.toRingHom = algebraMap A B)
    (hP : P.deltaStructure.IsPerfect) (hQ : Q.deltaStructure.IsPerfect) :
    B ⊗[A] P.ideal ≃ₗ[B] Q.ideal :=
  LinearEquiv.ofBijective (f.idealTensorMap hf) (f.idealTensorMap_bijective hf hP hQ)

/-- イデアル基底変換同型の台線形写像は標準乗法写像。 -/
@[simp] theorem idealTensorEquiv_toLinearMap (f : Hom P Q)
    (hf : f.toRingHom = algebraMap A B)
    (hP : P.deltaStructure.IsPerfect) (hQ : Q.deltaStructure.IsPerfect) :
    (f.idealTensorEquiv hf hP hQ).toLinearMap = f.idealTensorMap hf := rfl

/-- イデアルの基底変換から終域環への自然な乗法写像は単射。
忠実平坦性を仮定せず、prism射の生成元の剛性で得る。 -/
theorem idealTensorMap_subtype_injective (f : Hom P Q)
    (hf : f.toRingHom = algebraMap A B)
    (hP : P.deltaStructure.IsPerfect) (hQ : Q.deltaStructure.IsPerfect) :
    Function.Injective (Q.ideal.subtype.comp (f.idealTensorMap hf)) :=
  Subtype.val_injective.comp (f.idealTensorMap_bijective hf hP hQ).1

/-- 標準乗法写像の像は終域のprismイデアル全体。 -/
theorem idealTensorMap_subtype_range (f : Hom P Q)
    (hf : f.toRingHom = algebraMap A B)
    (hP : P.deltaStructure.IsPerfect) (hQ : Q.deltaStructure.IsPerfect) :
    LinearMap.range (Q.ideal.subtype.comp (f.idealTensorMap hf)) = Q.ideal := by
  rw [LinearMap.range_comp, LinearMap.range_eq_top.mpr (f.idealTensorMap_bijective hf hP hQ).2]
  simp

end Compatible

/-- 任意の具体的な完全prism射に、その射自身のA代数構造を使う基底変換同型。
別のAlgebraインスタンスや適合性の仮定を外から要求しない。 -/
def idealBaseChangeEquiv (f : Hom P Q)
    (hP : P.deltaStructure.IsPerfect) (hQ : Q.deltaStructure.IsPerfect) :
    letI := f.toRingHom.toAlgebra
    B ⊗[A] P.ideal ≃ₗ[B] Q.ideal := by
  letI := f.toRingHom.toAlgebra
  exact f.idealTensorEquiv rfl hP hQ

/-- 射自身のA代数構造による同型も、純テンソルでは標準乗法に一致する。 -/
@[simp] theorem idealBaseChangeEquiv_tmul (f : Hom P Q)
    (hP : P.deltaStructure.IsPerfect) (hQ : Q.deltaStructure.IsPerfect) (b : B) (x : P.ideal) :
    letI := f.toRingHom.toAlgebra
    (f.idealBaseChangeEquiv hP hQ (b ⊗ₜ[A] x) : B) = b * f.toRingHom x := rfl

end Hom
end SerrePositivity.BhattScholze.OrientedPrism
