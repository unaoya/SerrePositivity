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

/-- 普遍同相の対角射の核は nil。底変換後の Spec 単射性と乗法射の切断を使う。 -/
theorem nil_diagonal_of_isUniversalHomeomorphism {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B]
    (hf : IsUniversalHomeomorphism (algebraMap A B)) :
    RingHom.ker (Algebra.TensorProduct.lmul' A (S := B)).toRingHom ≤
      nilradical (B ⊗[A] B) := by
  let i : B →+* B ⊗[A] B := Algebra.TensorProduct.includeRight.toRingHom
  let m : B ⊗[A] B →+* B := (Algebra.TensorProduct.lmul' A).toRingHom
  have hi : IsUniversalHomeomorphism i :=
    isUniversalHomeomorphism_baseChange (algebraMap A B) (algebraMap A B) hf
  have hmi : m.comp i = RingHom.id B := by
    ext b
    simp [m, i]
  have hs : Function.Surjective (PrimeSpectrum.comap m) := by
    intro P
    refine ⟨PrimeSpectrum.comap i P, hi.radicial.1 ?_⟩
    rw [← PrimeSpectrum.comap_comp_apply, hmi]
    rfl
  exact (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical m).mp hs.denseRange

/-- 体値点の延長が一意なら、対角射の核は nil。
Spec 全射性は不要なので、局所化を合成した射にも適用できる。 -/
theorem nil_diagonal_of_injective_fieldMaps {A B : Type u}
    [CommRing A] [CommRing B] [Algebra A B]
    (hf : ∀ (K : Type u) [Field K],
      Function.Injective (fun g : B →+* K ↦ g.comp (algebraMap A B))) :
    RingHom.ker (Algebra.TensorProduct.lmul' A (S := B)).toRingHom ≤
      nilradical (B ⊗[A] B) := by
  intro z hz
  apply mem_nilradical.mpr
  apply nilpotent_iff_mem_prime.mpr
  intro P hP
  let : P.IsPrime := hP
  let K := P.ResidueField
  let q := algebraMap (B ⊗[A] B) K
  let a := q.comp (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toRingHom
  let b := q.comp (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom
  let m := (Algebra.TensorProduct.lmul' A (S := B)).toRingHom
  have hab : a = b := hf K (by simp [a, b, RingHom.comp_assoc])
  have hq : q = a.comp m := by
    apply Algebra.TensorProduct.ringHom_ext
    · ext x
      simp [a, m]
    · ext x
      simpa [a, b, m] using (RingHom.congr_fun hab x).symm
  apply (Ideal.algebraMap_residueField_eq_zero (I := P)).mp
  change q z = 0
  rw [hq, RingHom.comp_apply, show m z = 0 from hz, map_zero]

end SerrePositivity.CommutativeAlgebra
