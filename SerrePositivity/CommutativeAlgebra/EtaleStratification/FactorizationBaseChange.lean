module

public import SerrePositivity.CommutativeAlgebra.EtaleStratification.Factorization
public import SerrePositivity.CommutativeAlgebra.EtaleStratification.ReducedEtale
public import SerrePositivity.CommutativeAlgebra.UniversalHomeomorphism.PrincipalOpen

/-!
# 有限エタール分解の被約底変換

## 概要
被約な環への底変換の後に終域を被約化しても、有限エタール分解が存在する。

## 方針
有限エタール中間代数を底変換する。後半は普遍同相の底変換と nil な商の合成。
p 冪倍が像に入る性質はテンソル積の加法的帰納と商の全射性で移す。

## 規約
被約化は底変換の後に行う。

## 使われ方
Noetherian 近似上で選んだ層別を、元の基底へ移す。
-/

@[expose] public section
noncomputable section
universe u

namespace SerrePositivity.CommutativeAlgebra

open scoped TensorProduct

/-- p 冪倍が像に入る性質はテンソル積による底変換で保たれる。 -/
theorem power_surjective_tensorMap
    {R A B D : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing D]
    [Algebra R A] [Algebra R B] [Algebra R D] (p : ℕ) (f : A →ₐ[R] B)
    (hf : ∀ y : B, ∃ x : A, ∃ n : ℕ, f x = (p : B) ^ n * y) :
    ∀ y : B ⊗[R] D, ∃ x : A ⊗[R] D, ∃ n : ℕ,
      Algebra.TensorProduct.map f (AlgHom.id R D) x = (p : B ⊗[R] D) ^ n * y := by
  intro y
  suffices ∃ x : A ⊗[R] D, ∃ n : ℕ,
      Algebra.TensorProduct.map f (AlgHom.id R D) x = (p : R) ^ n • y by
    simpa only [Algebra.smul_def, map_pow, map_natCast] using this
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul b d =>
    obtain ⟨a, n, ha⟩ := hf b
    refine ⟨a ⊗ₜ[R] d, n, ?_⟩
    simp only [Algebra.TensorProduct.map_tmul, AlgHom.id_apply, ha,
      TensorProduct.smul_tmul', Algebra.smul_def, map_pow, map_natCast]
  | add x y hx hy =>
    obtain ⟨a, n, ha⟩ := hx
    obtain ⟨b, m, hb⟩ := hy
    refine ⟨(p : R) ^ m • a + (p : R) ^ n • b, n + m, ?_⟩
    simp only [map_add, map_smul, ha, hb, pow_add, mul_smul, smul_add]
    rw [smul_comm ((p : R) ^ m) ((p : R) ^ n)]

/-- 被約環への底変換の後に終域を被約化しても、有限エタール分解が存在する。 -/
theorem hasEtaleFactorization_reduced_baseChange
    {A B D : Type u} [CommRing A] [CommRing B] [CommRing D]
    [Algebra A B] [Algebra A D] [IsReduced D] (p : ℕ)
    (hf : HasEtaleFactorization p (algebraMap A B)) :
    HasEtaleFactorization p
      ((Ideal.Quotient.mk (nilradical (B ⊗[A] D))).comp
        (Algebra.TensorProduct.includeRight : D →ₐ[A] B ⊗[A] D).toRingHom) := by
  obtain ⟨T, a, b, hab, hfin, het, hu, hp⟩ := hf
  let : Algebra A T := a.toAlgebra
  let : Module.Finite A T := hfin
  let : Algebra.Etale A T := het
  let : Algebra T B := b.toAlgebra
  let : IsScalarTower A T B := IsScalarTower.of_algebraMap_eq fun x ↦
    (RingHom.congr_fun hab x).symm
  let T' := T ⊗[A] D
  let C := B ⊗[A] D
  let C' := C ⧸ nilradical C
  let : Algebra D T' := Algebra.TensorProduct.rightAlgebra
  let : Algebra D C := Algebra.TensorProduct.rightAlgebra
  let f : T →ₐ[A] B := { __ := b, commutes' := fun x ↦ RingHom.congr_fun hab x }
  let F : T' →ₐ[A] C := Algebra.TensorProduct.map f (AlgHom.id A D)
  let : Algebra T' C := F.toRingHom.toAlgebra
  let : IsScalarTower T T' C := IsScalarTower.of_algebraMap_eq fun x ↦ by
    simp only [T', C, F, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.map_tmul, AlgHom.id_apply, map_one]
    rfl
  let : Algebra.IsPushout T B T' C :=
    Algebra.IsPushout.tensorProduct_tensorProduct A D T B (by ext; simp [F])
  have hFU : IsUniversalHomeomorphism F.toRingHom :=
    isUniversalHomeomorphism_of_isPushout b (algebraMap T T') (algebraMap B C) F.toRingHom
      (CommRingCat.isPushout_of_isPushout T B T' C) hu
  have hfinite : (algebraMap D T').Finite :=
    RingHom.finite_isStableUnderBaseChange A T D T' hfin
  let : Module.Finite D T' := (RingHom.finite_algebraMap).mp hfinite
  have hetale : (algebraMap D T').Etale :=
    RingHom.Etale.isStableUnderBaseChange A T D T' het
  let : Algebra.Etale D T' := RingHom.etale_algebraMap.mp hetale
  let : IsReduced T' := isReduced_of_finite_etale D T'
  let q : C →+* C' := Ideal.Quotient.mk (nilradical C)
  let b' : T' →+* C' := q.comp F.toRingHom
  have hqU : IsUniversalHomeomorphism q :=
    isUniversalHomeomorphism_of_nil_kernel q Ideal.Quotient.mk_surjective (by simp [q])
  have hbU : IsUniversalHomeomorphism b' := isUniversalHomeomorphism_comp _ _ hFU hqU
  have hbI : Function.Injective b' := by
    rw [RingHom.injective_iff_ker_eq_bot]
    apply bot_unique
    have hnil := (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical b').mp hbU.surjective_spec.denseRange
    simpa only [nilradical_eq_zero, Ideal.zero_eq_bot] using hnil
  refine ⟨CommRingCat.of T', algebraMap D T', b', ?_, inferInstance, inferInstance, hbU,
    invertPrimeMap_injective p b' hbI, ?_⟩
  · ext d
    simp [b', F, T', C, q]
  · apply (invertPrimeMap_surjective_iff p b').mpr
    intro z
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective z
    obtain ⟨x, n, hx⟩ := power_surjective_tensorMap (D := D) p f
      ((invertPrimeMap_surjective_iff p b).mp hp.surjective) y
    refine ⟨x, n, ?_⟩
    change q (F x) = _
    rw [hx, map_mul, map_pow, map_natCast]

end SerrePositivity.CommutativeAlgebra
