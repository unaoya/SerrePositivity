module

public import SerrePositivity.CommutativeAlgebra.AdicCompletionOpenQuotient
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-! # 冪で零化される加群への完備化の基底変更

I のある冪で消える加群では、I 進完備化への基底変更は加群を変えない。
完備化の開イデアル商の評価を使い、基底環や完備環の Noether 性を要求しない。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity
open TensorProduct
open scoped TensorProduct
set_option backward.isDefEq.respectTransparency false

variable {R C M : Type u} [CommRing R] [CommRing C] [Algebra R C]
    [AddCommGroup M] [Module R M]

/-- I で消える加群とのテンソル積では、I の拡張イデアルの元が左因子にあると零となる。 -/
theorem tmul_eq_zero_of_mem_map_annihilator (I : Ideal R)
    (hM : Module.IsTorsionBySet R M I) (c : C)
    (hc : c ∈ I.map (algebraMap R C)) (m : M) : c ⊗ₜ[R] m = 0 := by
  rw [Ideal.map] at hc
  induction hc using Submodule.span_induction with
  | mem c hc =>
    obtain ⟨r, hr, rfl⟩ := hc
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
      hM (x := m) (a := ⟨r, hr⟩), tmul_zero]
  | zero => exact zero_tmul _ _
  | add x y _ _ hx hy => rw [add_tmul, hx, hy, add_zero]
  | smul c x _ hx =>
    change (c • x) ⊗ₜ[R] m = 0
    rw [← smul_tmul', hx, smul_zero]

/-- I の冪で消える加群を完備化へ送る標準テンソル写像は全単射。
逆向きの評価は完備化の開イデアル商を経由して構成する。 -/
theorem adicCompletion_tensor_one_bijective (I : Ideal R) (hI : I.FG) (n : ℕ)
    (hM : Module.IsTorsionBySet R M (I ^ n : Ideal R)) :
    Function.Bijective (TensorProduct.mk R (AdicCompletion I R) M 1) := by
  let Q := R ⧸ I ^ n
  let : Module Q M := hM.module
  let φ := adicCompletionOpenQuotientMap I (I ^ n) n le_rfl
  let : Module (AdicCompletion I R) M := Module.compHom M φ.toRingHom
  let : IsScalarTower R (AdicCompletion I R) M := by
    apply IsScalarTower.of_algebraMap_smul
    intro r m
    change φ (algebraMap R (AdicCompletion I R) r) • m = r • m
    rw [adicCompletionOpenQuotientMap_algebraMap]
    exact hM.mk_smul r m
  let E : (AdicCompletion I R) ⊗[R] M →ₗ[R] M :=
    TensorProduct.lift (Algebra.lsmul R R M (A := AdicCompletion I R)).toLinearMap
  have hleft : Function.LeftInverse E (TensorProduct.mk R (AdicCompletion I R) M 1) := by
    intro m
    change (1 : AdicCompletion I R) • m = m
    exact one_smul _ _
  refine ⟨hleft.injective, ?_⟩
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul c m =>
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (φ c)
    have hd : c - algebraMap R (AdicCompletion I R) r ∈
        (I ^ n).map (algebraMap R (AdicCompletion I R)) := by
      rw [← adicCompletionOpenQuotientMap_ker I (I ^ n) n le_rfl hI]
      change φ (c - algebraMap R (AdicCompletion I R) r) = 0
      rw [map_sub, adicCompletionOpenQuotientMap_algebraMap]
      exact sub_eq_zero.mpr hr.symm
    have ht := tmul_eq_zero_of_mem_map_annihilator (I ^ n) hM _ hd m
    rw [sub_tmul, sub_eq_zero] at ht
    refine ⟨r • m, ?_⟩
    change (1 : AdicCompletion I R) ⊗ₜ[R] (r • m) = c ⊗ₜ[R] m
    rw [ht, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨mx, hmx⟩ := hx
    obtain ⟨my, hmy⟩ := hy
    exact ⟨mx + my, by rw [map_add, hmx, hmy]⟩

/-- 冪ねじれ加群への完備化の基底変更を、基底環上の線形同値として公開する。 -/
def adicCompletionTorsionTensorEquiv (I : Ideal R) (hI : I.FG) (n : ℕ)
    (hM : Module.IsTorsionBySet R M (I ^ n : Ideal R)) :
    (AdicCompletion I R) ⊗[R] M ≃ₗ[R] M :=
  (LinearEquiv.ofBijective (TensorProduct.mk R (AdicCompletion I R) M 1)
    (adicCompletion_tensor_one_bijective I hI n hM)).symm

end SerrePositivity
