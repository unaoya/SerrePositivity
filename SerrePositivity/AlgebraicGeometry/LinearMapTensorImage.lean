module

public import SerrePositivity.AlgebraicGeometry.IdealTensorMap

/-!
概要：KST §5、Stacks 0815 の有限加群から環への写像の基底変更と像。
方針：包含の場合と同じ乗法型のテンソル写像を構成する。
規約：像は元の環のイデアルとして扱う。
使われ方：境界外で階数一自由な加群の純変換の比較。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable {R C M : Type*} [CommRing R] [CommRing C] [Algebra R C]
  [AddCommGroup M] [Module R M] (g : M →ₗ[R] R)

/--
概要：環を標的とする線形写像を基底変更して係数環を標的に戻す。
方針：基底変更にテンソル積の右単位同型を合成する。
規約：KST §5、Stacks 0815、基底変更は任意。
使われ方：純変換と像イデアルの比較。
-/
def linearMapTensorToAlgebra : C ⊗[R] M →ₗ[C] C :=
  (TensorProduct.AlgebraTensorModule.rid R C C).toLinearMap ∘ₗ g.baseChange C

/--
概要：環を標的とする基底変更写像の純テンソル上の値。
方針：右単位同型の公式を使う。
規約：KST §5、Stacks 0815、積の順序を固定する。
使われ方：像と核の直接計算。
-/
@[simp] theorem linearMapTensorToAlgebra_tmul (c : C) (m : M) :
    linearMapTensorToAlgebra g (c ⊗ₜ m) = c * algebraMap R C (g m) := by
  simp [linearMapTensorToAlgebra, Algebra.smul_def, mul_comm]

/--
概要：基底変更した写像の像は元の像イデアルの拡大。
方針：純テンソルの像と元の写像の値を生成元として比較する。
規約：KST §5、Stacks 0815、平坦性を使わない像の等式。
使われ方：元の加群をイデアルの平坦化へ還元する。
-/
theorem linearMapTensorToAlgebra_range :
    LinearMap.range (linearMapTensorToAlgebra (C := C) g) =
      Ideal.map (algebraMap R C) (LinearMap.range g) := by
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | tmul c m =>
      rw [linearMapTensorToAlgebra_tmul]
      exact Ideal.mul_mem_left _ c (Ideal.mem_map_of_mem _ ⟨m, rfl⟩)
    | add x y hx hy => simpa using (Ideal.map (algebraMap R C) (LinearMap.range g)).add_mem hx hy
  · apply Ideal.map_le_iff_le_comap.mpr
    rintro _ ⟨m, rfl⟩
    exact ⟨1 ⊗ₜ m, by simp⟩

/--
概要：互いに分母倍で逆な写像の基底変更では、環への写像の核が同じ分母で消える。
方針：基底変更の関手性で合成式を移し、右単位同型の単射性を使う。
規約：KST §5、Stacks 0815、必要なのは加群側の一方の合成式。
使われ方：分母倍同型から純変換の像への同型を得る。
-/
theorem linearMapTensorToAlgebra_ker_annihilated
    (h : R →ₗ[R] M) (r : R) (hh : h.comp g = r • LinearMap.id)
    (z : C ⊗[R] M) (hz : linearMapTensorToAlgebra g z = 0) :
    algebraMap R C r • z = 0 := by
  have hgzero : g.baseChange C z = 0 := by
    apply (TensorProduct.AlgebraTensorModule.rid R C C).injective
    exact hz.trans (map_zero _).symm
  have heq := congrArg (fun k : M →ₗ[R] M => k.baseChange C) hh
  rw [LinearMap.baseChange_comp, LinearMap.baseChange_smul, LinearMap.baseChange_id] at heq
  have hz' := LinearMap.congr_fun heq z
  simpa only [LinearMap.comp_apply, hgzero, map_zero, LinearMap.smul_apply,
    LinearMap.id_apply, algebraMap_smul] using hz'.symm

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
