module

public import SerrePositivity.CommutativeAlgebra.EtaleStratification.ReducedTensorProduct
public import SerrePositivity.CommutativeAlgebra.EtaleStratification.FactorizationBaseChange

/-!
# 被約層と底変換の比較

## 概要
層の底変換の被約化は、底変換後の環で同じ元から作った層と標準的に同型。

## 方針
被約主開層の普遍性を使って双方向の射を構成し、元の環の像上で逆であることを確認する。

## 規約
終域のイデアルは、基底のイデアルを底変換先に延長した後で根基を取る。

## 使われ方
Noetherian 近似上で構成した有限エタール層別の底変換。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.CommutativeAlgebra

open scoped TensorProduct

/-- 層の被約底変換と、底変換した環の層の標準同型。 -/
theorem exists_stratum_reduced_baseChange_equiv
    (R S D : Type u) [CommRing R] [CommRing S] [CommRing D]
    [Algebra R S] [Algebra R D] (I : Ideal R) (g : R) :
    let A := StratumRing I g
    let B := StratumRing (I.map (algebraMap R S)) (algebraMap R S g)
    let D₀ := StratumRing (I.map (algebraMap R D)) (algebraMap R D g)
    letI : Algebra A B := (stratumMap (algebraMap R S) I g).toAlgebra
    letI : Algebra A D₀ := (stratumMap (algebraMap R D) I g).toAlgebra
    let C := S ⊗[R] D
    letI : Algebra D C := Algebra.TensorProduct.rightAlgebra
    let J := (I.map (algebraMap R D)).map (algebraMap D C)
    ∃ e : ((B ⊗[A] D₀) ⧸ nilradical (B ⊗[A] D₀)) ≃+*
        StratumRing J (algebraMap D C (algebraMap R D g)),
      e.toRingHom.comp ((Ideal.Quotient.mk (nilradical (B ⊗[A] D₀))).comp
        (Algebra.TensorProduct.includeRight : D₀ →ₐ[A] B ⊗[A] D₀).toRingHom) =
          stratumMap (algebraMap D C) (I.map (algebraMap R D)) (algebraMap R D g) := by
  let A := StratumRing I g
  let Iₛ := I.map (algebraMap R S)
  let Iₙ := I.map (algebraMap R D)
  let B := StratumRing Iₛ (algebraMap R S g)
  let D₀ := StratumRing Iₙ (algebraMap R D g)
  let α := stratumMap (algebraMap R S) I g
  let β := stratumMap (algebraMap R D) I g
  let : Algebra A B := α.toAlgebra
  let : Algebra A D₀ := β.toAlgebra
  let C := S ⊗[R] D
  let : Algebra D C := Algebra.TensorProduct.rightAlgebra
  let J := Iₙ.map (algebraMap D C)
  let h := algebraMap D C (algebraMap R D g)
  let E := StratumRing J h
  let : IsReduced E := isReduced_stratumRing J h
  let γ : D₀ →+* E := stratumMap (algebraMap D C) Iₙ (algebraMap R D g)
  let j : S →+* C := Algebra.TensorProduct.includeLeft.toRingHom
  have hj (x : R) : j (algebraMap R S x) = algebraMap D C (algebraMap R D x) := by
    exact Algebra.TensorProduct.tmul_one_eq_one_tmul x
  let s : S →+* E := (stratumUnit J h).comp j
  have hsI : Iₛ ≤ RingHom.ker s := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change stratumUnit J h (j (algebraMap R S x)) = 0
    rw [hj]
    exact stratumUnit_ker J h (Ideal.mem_map_of_mem _ (Ideal.mem_map_of_mem _ hx))
  have hsg : IsUnit (s (algebraMap R S g)) := by
    change IsUnit (stratumUnit J h (j (algebraMap R S g)))
    rw [hj]
    exact stratumUnit_isUnit J h
  let u : B →+* E := stratumLift Iₛ (algebraMap R S g) s hsI hsg
  have huγ : u.comp α = γ.comp β := by
    apply stratumRing_hom_ext I g
    intro x
    simp only [RingHom.comp_apply, u, α, β, γ, stratumMap_unit, stratumLift_unit]
    change stratumUnit J h (j (algebraMap R S x)) =
      stratumUnit J h (algebraMap D C (algebraMap R D x))
    rw [hj]
  let P := B ⊗[A] D₀
  let P₀ := P ⧸ nilradical P
  let : IsReduced P₀ := isReduced_reduction P
  let q₀ : P →+* P₀ := Ideal.Quotient.mk (nilradical P)
  let qraw : P →+* E := tensorRingLift u γ huγ
  let q : P₀ →+* E := reductionLift qraw
  let l : B →+* P := Algebra.TensorProduct.includeLeft.toRingHom
  let r : D₀ →+* P := Algebra.TensorProduct.includeRight.toRingHom
  let kₛ : S →+* P₀ := (q₀.comp l).comp (stratumUnit Iₛ (algebraMap R S g))
  let kₙ : D →+* P₀ := (q₀.comp r).comp (stratumUnit Iₙ (algebraMap R D g))
  have hk : kₛ.comp (algebraMap R S) = kₙ.comp (algebraMap R D) := by
    ext x
    change q₀ (l (stratumUnit Iₛ (algebraMap R S g) (algebraMap R S x))) =
      q₀ (r (stratumUnit Iₙ (algebraMap R D g) (algebraMap R D x)))
    rw [← stratumMap_unit, ← stratumMap_unit]
    exact congrArg q₀ (Algebra.TensorProduct.tmul_one_eq_one_tmul (stratumUnit I g x))
  let k : C →+* P₀ := tensorRingLift kₛ kₙ hk
  have hkD (x : D) : k (algebraMap D C x) = kₙ x := by
    change tensorRingLift kₛ kₙ hk ((1 : S) ⊗ₜ[R] x) = _
    simp only [tensorRingLift_tmul, map_one, one_mul]
  have hkS (x : S) : k (j x) = kₛ x := by
    change tensorRingLift kₛ kₙ hk (x ⊗ₜ[R] (1 : D)) = _
    simp only [tensorRingLift_tmul, map_one, mul_one]
  have hkI : J ≤ RingHom.ker k := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change k (algebraMap D C x) = 0
    rw [hkD]
    change q₀ (r (stratumUnit Iₙ (algebraMap R D g) x)) = 0
    rw [stratumUnit_ker Iₙ (algebraMap R D g) hx, map_zero, map_zero]
  have hkg : IsUnit (k h) := by
    rw [hkD]
    exact ((stratumUnit_isUnit Iₙ (algebraMap R D g)).map r).map q₀
  let v : E →+* P₀ := stratumLift J h k hkI hkg
  have hvqraw : v.comp qraw = q₀ := by
    apply Algebra.TensorProduct.ringHom_ext
    · apply stratumRing_hom_ext Iₛ (algebraMap R S g)
      intro x
      simp only [RingHom.comp_apply, qraw, tensorRingLift_tmul, map_one, mul_one,
        u, stratumLift_unit, s]
      change v (stratumUnit J h (j x)) = q₀ (l (stratumUnit Iₛ (algebraMap R S g) x))
      rw [v, stratumLift_unit, hkS]
      rfl
    · apply stratumRing_hom_ext Iₙ (algebraMap R D g)
      intro x
      simp only [RingHom.comp_apply, qraw, tensorRingLift_tmul, map_one, one_mul,
        γ, stratumMap_unit]
      change v (stratumUnit J h (algebraMap D C x)) =
        q₀ (r (stratumUnit Iₙ (algebraMap R D g) x))
      rw [v, stratumLift_unit, hkD]
      rfl
  have hvq : Function.LeftInverse v q := by
    intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    change v (reductionLift qraw (Ideal.Quotient.mk (nilradical P) z)) = q₀ z
    rw [reductionLift_mk]
    exact RingHom.congr_fun hvqraw z
  have hqk : q.comp k = stratumUnit J h := by
    apply Algebra.TensorProduct.ringHom_ext
    · ext x
      change q (k (j x)) = stratumUnit J h (j x)
      rw [hkS]
      change reductionLift qraw (q₀ (l (stratumUnit Iₛ (algebraMap R S g) x))) = _
      simp only [q₀, reductionLift_mk, qraw, l, tensorRingLift_tmul, map_one, mul_one,
        u, stratumLift_unit]
      rfl
    · ext x
      change q (k (algebraMap D C x)) = stratumUnit J h (algebraMap D C x)
      rw [hkD]
      change reductionLift qraw (q₀ (r (stratumUnit Iₙ (algebraMap R D g) x))) = _
      simp only [q₀, reductionLift_mk, qraw, r, tensorRingLift_tmul, map_one, one_mul,
        γ, stratumMap_unit]
  have hqv : Function.RightInverse v q := by
    have he : q.comp v = RingHom.id E := by
      apply stratumRing_hom_ext J h
      intro x
      change q (v (stratumUnit J h x)) = stratumUnit J h x
      rw [v, stratumLift_unit]
      exact RingHom.congr_fun hqk x
    exact fun x ↦ RingHom.congr_fun he x
  refine ⟨RingEquiv.ofBijective q ⟨hvq.injective, hqv.surjective⟩, ?_⟩
  ext x
  change reductionLift qraw (q₀ ((1 : B) ⊗ₜ[A] x)) = γ x
  simp only [q₀, reductionLift_mk, qraw, tensorRingLift_tmul, map_one, one_mul]

/-- 有限エタール分解を持つ層は、基底の底変換後も同じ分解を持つ。 -/
theorem hasEtaleFactorization_stratum_baseChange
    (R S D : Type u) [CommRing R] [CommRing S] [CommRing D]
    [Algebra R S] [Algebra R D] (p : ℕ) (I : Ideal R) (g : R)
    (hf : HasEtaleFactorization p (stratumMap (algebraMap R S) I g)) :
    letI : Algebra D (S ⊗[R] D) := Algebra.TensorProduct.rightAlgebra
    HasEtaleFactorization p (stratumMap (algebraMap D (S ⊗[R] D))
      (I.map (algebraMap R D)) (algebraMap R D g)) := by
  let A := StratumRing I g
  let B := StratumRing (I.map (algebraMap R S)) (algebraMap R S g)
  let D₀ := StratumRing (I.map (algebraMap R D)) (algebraMap R D g)
  let : Algebra A B := (stratumMap (algebraMap R S) I g).toAlgebra
  let : Algebra A D₀ := (stratumMap (algebraMap R D) I g).toAlgebra
  let : IsReduced D₀ := isReduced_stratumRing _ _
  let : Algebra D (S ⊗[R] D) := Algebra.TensorProduct.rightAlgebra
  have h := hasEtaleFactorization_reduced_baseChange (A := A) (B := B) (D := D₀) p hf
  obtain ⟨e, he⟩ := exists_stratum_reduced_baseChange_equiv R S D I g
  have ht := hasEtaleFactorization_transport p (RingEquiv.refl D₀) e _ h
  simpa only [RingEquiv.symm_refl, RingEquiv.toRingHom_refl', RingHom.comp_id, he] using ht

end SerrePositivity.CommutativeAlgebra
