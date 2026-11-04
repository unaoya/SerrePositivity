module

public import SerrePositivity.CommutativeAlgebra.UniversalHomeomorphism.Basic

/-!
# 対角射の nil な核による普遍同相の判定

## 概要
整かつ Spec 全射な射について、テンソル積の乗法射の核が nil なら普遍同相。

## 方針
二つの体値点からテンソル積の体値点を作り、対角差の冪零性から二点の一致を得る。

## 規約
nil は各元が冪零という意味であり、イデアルの冪零性を仮定しない。

## 使われ方
一般点での radicial 性を有限個の関係として主開集合へ延ばす。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.CommutativeAlgebra

open scoped TensorProduct

/-- 乗法射の核が nil なら、整な Spec 全射は普遍同相。 -/
theorem isUniversalHomeomorphism_of_nil_diagonal {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B]
    (hi : (algebraMap A B).IsIntegral)
    (hs : Function.Surjective (PrimeSpectrum.comap (algebraMap A B)))
    (hker : RingHom.ker (Algebra.TensorProduct.lmul' A (S := B)).toRingHom ≤
      nilradical (B ⊗[A] B)) : IsUniversalHomeomorphism (algebraMap A B) := by
  apply isUniversalHomeomorphism_of_injective_fieldMaps _ hi hs
  intro K _ g₁ g₂ he
  let : Algebra A K := (g₁.comp (algebraMap A B)).toAlgebra
  let φ : B →ₐ[A] K := { __ := g₁, commutes' := fun _ ↦ rfl }
  let ψ : B →ₐ[A] K :=
    { __ := g₂, commutes' := fun r ↦ (congrArg (fun h : A →+* K ↦ h r) he).symm }
  let t : B ⊗[A] B →ₐ[A] K :=
    Algebra.TensorProduct.lift φ ψ fun _ _ ↦ Commute.all _ _
  ext b
  have hn : IsNilpotent (b ⊗ₜ[A] (1 : B) - (1 : B) ⊗ₜ[A] b) :=
    mem_nilradical.mp (hker (by simp [RingHom.mem_ker]))
  have hz := (hn.map t).eq_zero
  apply sub_eq_zero.mp
  simpa [t, φ, ψ] using hz

end SerrePositivity.CommutativeAlgebra
