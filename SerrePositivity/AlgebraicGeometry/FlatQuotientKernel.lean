module

public meta import SerrePositivity.Util.DeprecatedAlias
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
概要：KST §5、Stacks 05CG・05D3 の平坦な終域を持つ全射の核とイデアル倍の交わり。
方針：商環とのテンソルの単射性を、商テンソル同型でイデアル倍の逆像へ移す。
規約：加群の有限性と基礎環の Noether 性を課さない。
使われ方：剰余の右逆から自由加群の自己準同型を作り、核上で冪零性を使う。
-/

@[expose] public noncomputable section
universe u
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

/--
概要：商環とのテンソルで単射な線形写像は、そのイデアル倍の逆像を正確に保つ。
方針：一と元の純テンソルの零を、商テンソル同型の両側で読む。
規約：KST §5、Stacks 05CG、元の写像の単射性は別に仮定しない。
使われ方：平坦な終域を持つ全射の核とイデアル倍の交わり。
-/
theorem smul_top_comap_eq_of_lTensor_quotient_injective
    {R K F : Type u} [CommRing R] [AddCommGroup K] [Module R K]
    [AddCommGroup F] [Module R F] (I : Ideal R) (e : K →ₗ[R] F)
    (he : Function.Injective (e.lTensor (R ⧸ I))) :
    (I • (⊤ : Submodule R F)).comap e = I • (⊤ : Submodule R K) := by
  apply le_antisymm
  · intro x hx
    have hz : (TensorProduct.quotTensorEquivQuotSMul F I)
        (e.lTensor (R ⧸ I) ((1 : R ⧸ I) ⊗ₜ[R] x)) = 0 := by
      simp only [LinearMap.lTensor_tmul,
        TensorProduct.quotTensorEquivQuotSMul_mk_one_tmul]
      change e x ∈ LinearMap.ker (I • (⊤ : Submodule R F)).mkQ
      rw [Submodule.ker_mkQ]
      exact hx
    have ht : e.lTensor (R ⧸ I) ((1 : R ⧸ I) ⊗ₜ[R] x) = 0 :=
      (TensorProduct.quotTensorEquivQuotSMul F I).injective (by simpa using hz)
    have hs : (1 : R ⧸ I) ⊗ₜ[R] x = 0 := he (by simpa using ht)
    have hq : (I • (⊤ : Submodule R K)).mkQ x = 0 := by
      simpa using congrArg (TensorProduct.quotTensorEquivQuotSMul K I) hs
    change x ∈ LinearMap.ker (I • (⊤ : Submodule R K)).mkQ at hq
    rwa [Submodule.ker_mkQ] at hq
  · intro x hx
    change e x ∈ I • (⊤ : Submodule R F)
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro r hr k hk
      rw [map_smul]
      exact Submodule.smul_mem_smul hr (Submodule.mem_top)
    · intro x y hx hy
      simpa using (I • (⊤ : Submodule R F)).add_mem hx hy

/--
概要：平坦な終域を持つ全射の核 K について K∩IF は IK に一致する。
方針：完全列の核包含を商環とテンソルした単射性を、イデアル倍の逆像の判定へ渡す。
規約：KST §5、Stacks 05CG・05D3、等式は核を加群とした部分加群の等式。
使われ方：自由加群の自己準同型による核のイデアル倍への縮小。
-/
theorem smul_top_comap_kernel_subtype_of_flat
    {R F M : Type u} [CommRing R] [AddCommGroup F] [Module R F]
    [AddCommGroup M] [Module R M] [Module.Flat R M]
    (π : F →ₗ[R] M) (hπ : Function.Surjective π) (I : Ideal R) :
    (I • (⊤ : Submodule R F)).comap (LinearMap.ker π).subtype =
      I • (⊤ : Submodule R (LinearMap.ker π)) :=
  smul_top_comap_eq_of_lTensor_quotient_injective I _
    (LinearMap.lTensor_injective_of_exact_of_flat π hπ _
      (Submodule.injective_subtype _) (LinearMap.exact_subtype_ker_map π) (R ⧸ I))

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
