module

public import SerrePositivity.CommutativeAlgebra.HenselianFinite
public import SerrePositivity.CommutativeAlgebra.SeparableBaseChange
public import Mathlib.RingTheory.DedekindDomain.IntegralClosure
public import Mathlib.RingTheory.Invariant.Galois
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.FieldTheory.Normal.Closure
public import Mathlib.FieldTheory.SeparableClosure

/-!
# 正規な完備基底上のガロア正規化

## 概要

有限で生成点で分離的な整域拡大 `A → D` を、有限群作用を持つ整域拡大へ埋め込む。
分数体拡大の正規閉包を取り、その中の `A` の整閉包を構成する。
基底 `A` の正規性と Noether 性から整閉包の有限性を得て、完備性から局所性を導く。
ガロア理論と正規性から不変環は `A` であり、代数閉な剰余体も変わらない。

## 入力境界

`IsIntegrallyClosed A` は明示的な仮定である。正則局所環の正規性の証明を含めない。
正規化基底を選ぶ定理や長さ代数の存在定理には依存しない。
§5 ではこの構成を二つの素イデアル商に適用する。
-/

public section

universe u

namespace SerrePositivity

open IsLocalRing

set_option synthInstance.maxSize 2048

/-- 分離拡大の正規閉包は分離的である。
各埋め込みの像が分離的であることを確認し、それらの合成体としての定義を使う。 -/
theorem isSeparable_normalClosure
    (K L Ω : Type u) [Field K] [Field L] [Field Ω]
    [Algebra K L] [Algebra K Ω] [Algebra.IsSeparable K L] :
    Algebra.IsSeparable K (IntermediateField.normalClosure K L Ω) := by
  have (f : L →ₐ[K] Ω) : Algebra.IsSeparable K f.fieldRange :=
    Algebra.IsSeparable.of_algHom K L f.equivFieldRange.symm.toAlgHom
  unfold IntermediateField.normalClosure
  infer_instance

/-- 正規な完備ネーター局所基底上の有限分離整域拡大を、ガロア群作用付きの有限局所拡大へ上げる。
結論の自己同型群は有限で、不変元は全て基底から来る。基底の剰余体が代数閉なので、
新しい環の剰余体への基底からの写像も全射となる。整閉包の有限性は有限分離拡大に関する
トレースの一般論で十分であり、優秀環の一般論は使わない。 -/
theorem exists_galoisNormalization_of_normal_base
    (A D : Type u) [CommRing A] [IsDomain A] [IsIntegrallyClosed A]
    [IsNoetherianRing A] [IsLocalRing A] [IsAdicComplete (maximalIdeal A) A]
    [IsAlgClosed (ResidueField A)]
    [CommRing D] [IsDomain D] [Algebra A D] [Module.Finite A D]
    (hinj : Function.Injective (algebraMap A D))
    (hsep : ∀ d : D, ((minpoly A d).map (algebraMap A (FractionRing A))).Separable) :
    ∃ (B : Type u) (_ : CommRing B) (_ : IsDomain B) (_ : IsLocalRing B)
      (_ : IsAdicComplete (maximalIdeal B) B) (_ : Algebra A B) (_ : Algebra D B)
      (_ : IsScalarTower A D B),
      Module.Finite A B ∧ Module.Finite D B ∧
      Function.Injective (algebraMap D B) ∧
      Function.Surjective ((residue B).comp (algebraMap A B)) ∧
      (∀ b : B, ((minpoly A b).map (algebraMap A (FractionRing A))).Separable) ∧
      Finite (B ≃ₐ[A] B) ∧
      (∀ b : B, (∀ g : B ≃ₐ[A] B, g b = b) → b ∈ Set.range (algebraMap A B)) := by
  classical
  let : Module.IsTorsionFree A D := Module.isTorsionFree_iff_algebraMap_injective.mpr hinj
  let K := FractionRing A
  let L := FractionRing D
  let : Algebra K L := FractionRing.liftAlgebra A L
  let : IsScalarTower A K L := FractionRing.isScalarTower_liftAlgebra A L
  let : FiniteDimensional K L := finiteDimensional_fractionRing_of_finite A D K L
  let : Algebra.IsSeparable K L := isSeparable_fractionRing_of_separable_minpoly A D K L hsep
  let Ω := AlgebraicClosure L
  let E := IntermediateField.normalClosure K L Ω
  let : Algebra.IsSeparable K E := isSeparable_normalClosure K L Ω
  let : IsGalois K E := ⟨⟩
  let : Algebra A E := ((algebraMap K E).comp (algebraMap A K)).toAlgebra
  let : IsScalarTower A K E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Algebra D E := ((algebraMap L E).comp (algebraMap D L)).toAlgebra
  let : IsScalarTower D L E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : IsScalarTower A L E := IsScalarTower.to₁₃₄ A K L E
  let : IsScalarTower A D E := IsScalarTower.to₁₂₄ A D L E
  let B := integralClosure A E
  let f : D →ₐ[A] B :=
    (IsScalarTower.toAlgHom A D E).codRestrict B (fun d ↦
      (isIntegral_algHom_iff (IsScalarTower.toAlgHom A D E)
        ((algebraMap L E).injective.comp (IsFractionRing.injective D L))).mpr
        (Algebra.IsIntegral.isIntegral (R := A) d))
  let : Algebra D B := f.toRingHom.toAlgebra
  let : IsScalarTower A D B := IsScalarTower.of_algebraMap_eq fun a ↦ (f.commutes a).symm
  let : IsScalarTower D B E := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  let : Module.Finite A B := IsIntegralClosure.finite A K E B
  let : Module.Finite D B := Module.Finite.right A D B
  let : IsFractionRing B E := IsIntegralClosure.isFractionRing_of_finite_extension A K E B
  let : IsIntegrallyClosed B := integralClosure.isIntegrallyClosedOfFiniteExtension K
  let : Finite (B ≃ₐ[A] B) :=
    Finite.of_equiv (E ≃ₐ[K] E) (galRestrict A K E B).toEquiv
  let : IsLocalRing B := isLocalRing_finite_domain_of_complete A B
  let : IsAdicComplete (maximalIdeal B) B := isAdicComplete_finite_local_algebra (R := A) B
  refine ⟨B, inferInstance, inferInstance, inferInstance, inferInstance,
    inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_,
    residue_surjective_of_finite_of_isAlgClosed A B, ?_, inferInstance, ?_⟩
  · intro x y hxy
    exact ((algebraMap L E).injective.comp (IsFractionRing.injective D L))
      (congrArg (algebraMap B E) hxy)
  · exact (separable_minpoly_iff_fractionRing A B K E).mpr inferInstance
  · exact (Algebra.isInvariant_of_isGalois' A K E B).1

end SerrePositivity
