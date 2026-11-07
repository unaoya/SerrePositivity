module

public import SerrePositivity.AlgebraicGeometry.PureTransformExact
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
概要：境界元の冪で割っても左側の単射が保たれる場合、純変換は完全列を保つ。
方針：右端で境界ねじれになる元の持ち上げを、左端の元を引いて境界ねじれにする。
規約：左側の写像について、境界元の冪に関する可除性を明示する。
使われ方：台の次元による平坦化の帰納で、自由加群を除く完全列を純変換へ移す。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open scoped Pointwise TensorProduct

/--
概要：左側の写像が境界元の冪による可除性を反映するとき、中央の完全性は純変換に移る。
方針：右端でねじれになる元の冪倍を左端に持ち上げ、その冪で割った元を引く。
規約：右端の加群で境界元が正則に作用するという仮定を置かない。
使われ方：任意の基底変更で単射を保つ左側の写像に、境界の冪による商を適用する。
-/
theorem modulePureTransformMap_exact_of_reflects_pow_smul
    {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (f : R)
    (g : M →ₗ[R] N) (h : N →ₗ[R] P) (hex : Function.Exact g h)
    (hdiv : ∀ (k : ℕ) (m : M) (n : N), g m = (f ^ k) • n → ∃ m', m = (f ^ k) • m') :
    Function.Exact (modulePureTransformMap f g) (modulePureTransformMap f h) := by
  intro x
  obtain ⟨n, rfl⟩ := Submodule.Quotient.mk_surjective (boundaryTorsion f N) x
  constructor
  · intro hx
    have htor : h n ∈ boundaryTorsion f P := (Submodule.Quotient.mk_eq_zero _).mp hx
    obtain ⟨k, hk⟩ := (mem_boundaryTorsion_iff f P _).mp htor
    obtain ⟨m, hm⟩ := (hex ((f ^ k) • n)).mp (by rw [h.map_smul, hk])
    obtain ⟨m', hm'⟩ := hdiv k m n hm
    have ht : n - g m' ∈ boundaryTorsion f N := by
      apply (mem_boundaryTorsion_iff f N _).mpr
      refine ⟨k, ?_⟩
      rw [smul_sub, ← hm, ← g.map_smul, ← hm', sub_self]
    refine ⟨Submodule.Quotient.mk m', ?_⟩
    rw [modulePureTransformMap_mk]
    exact ((Submodule.Quotient.eq _).mpr ht).symm
  · rintro ⟨x, hx⟩
    obtain ⟨m, rfl⟩ := Submodule.Quotient.mk_surjective (boundaryTorsion f M) x
    rw [← hx, modulePureTransformMap_mk, modulePureTransformMap_mk]
    have hz := (hex (g m)).mpr ⟨m, rfl⟩
    simp only [hz, Submodule.Quotient.mk_zero]

/--
概要：基底を境界元の任意の冪で割っても左の写像が単射なら、純変換は完全列を保つ。
方針：商環とのテンソル積を加群の商と比較し、可除性を元の加群に戻す。
規約：左の写像が任意の基底変更で単射となる場合に、この仮定が使える。
使われ方：台の次元で帰納する平坦化で、自由加群を除く列の純変換。
-/
theorem modulePureTransformMap_exact_of_quotient_lTensor_injective
    {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (f : R)
    (g : M →ₗ[R] N) (h : N →ₗ[R] P) (hex : Function.Exact g h)
    (hinj : ∀ k : ℕ, Function.Injective (g.lTensor (R ⧸ Ideal.span {f ^ k}))) :
    Function.Exact (modulePureTransformMap f g) (modulePureTransformMap f h) := by
  apply modulePureTransformMap_exact_of_reflects_pow_smul f g h hex
  intro k m n he
  let I : Ideal R := Ideal.span {f ^ k}
  have hN : g m ∈ I • (⊤ : Submodule R N) := by
    change g m ∈ Ideal.span {f ^ k} • (⊤ : Submodule R N)
    rw [Submodule.ideal_span_singleton_smul, he]
    exact Submodule.smul_mem_pointwise_smul _ _ _ Submodule.mem_top
  have hzero : (1 : R ⧸ I) ⊗ₜ[R] m = 0 := by
    apply hinj k
    apply (TensorProduct.quotTensorEquivQuotSMul N I).injective
    rw [LinearMap.lTensor_tmul, map_zero, map_zero,
      TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
    exact (Submodule.Quotient.mk_eq_zero _).mpr hN
  have hM : m ∈ Ideal.span {f ^ k} • (⊤ : Submodule R M) := by
    apply (Submodule.Quotient.mk_eq_zero _).mp
    rw [← TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul I m, hzero, map_zero]
  rw [Submodule.ideal_span_singleton_smul] at hM
  obtain ⟨m', _, hm'⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).mp hM
  exact ⟨m', hm'.symm⟩

end SerrePositivity.AlgebraicGeometry
