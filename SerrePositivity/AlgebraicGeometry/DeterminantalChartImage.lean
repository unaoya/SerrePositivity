module

public import SerrePositivity.AlgebraicGeometry.DeterminantalChartColumns
public import SerrePositivity.AlgebraicGeometry.LinearMapTensorToPi
public import SerrePositivity.AlgebraicGeometry.PureTransformImage
public import SerrePositivity.AlgebraicGeometry.ChartBoundaryRegular

/-!
概要：KST §5、Stacks 0815 の行列式チャート上での像加群と純変換の自由化。
方針：Cramer の計算を純テンソルの生成性で拡張し、核の冪消滅で純変換へ移す。
規約：有限自由加群側への実際の写像と冪倍の左逆元を指定する。
使われ方：境界外で有限階数自由な有限加群の平坦化。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped TensorProduct

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [DecidableEq ι] (g : M →ₗ[R] (ι → R)) (m : ι → M)

/--
概要：行列式チャート上の像加群は指定した列の線形写像の像と等しい。
方針：純テンソルからの包含と、選んだ列の純テンソルによる持ち上げを使う。
規約：KST §5、Stacks 0815、チャートの代数構造は係数写像。
使われ方：像加群の自由化。
-/
theorem determinantalChart_tensor_range :
    let I := determinantalCenter g
    let a := determinantalCenterGenerator g m
    letI : Algebra R (BlowupChartRing I a) := (chartBaseMap I a).toAlgebra
    LinearMap.range (linearMapTensorToPi (C := BlowupChartRing I a) g) =
      LinearMap.range (determinantalChartColumns g m).mulVecLin := by
  let I := determinantalCenter g
  let a := determinantalCenterGenerator g m
  let : Algebra R (BlowupChartRing I a) := (chartBaseMap I a).toAlgebra
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    induction z using TensorProduct.inductionOn with
    | tmul c x =>
      rw [linearMapTensorToPi_tmul]
      exact (LinearMap.range (determinantalChartColumns g m).mulVecLin).smul_mem c
        (determinantalChartColumns_vector_mem_range g m x)
    | add x y hx hy =>
      simpa using (LinearMap.range (determinantalChartColumns g m).mulVecLin).add_mem hx hy
  · rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    refine ⟨1 ⊗ₜ m j, ?_⟩
    ext i
    simp [linearMapTensorToPi_tmul, determinantalChartColumns, imageColumnMatrix]
    rfl

/--
概要：行列式チャート上の純変換は指定された有限階数の自由加群と線形同型。
方針：核を境界ねじれと同定し、像を独立な列の像に同定する。
規約：KST §5、Stacks 0815、境界元は基礎環で正則とする。
使われ方：有限階数自由な境界外部分を持つ加群の平坦化の実際の同型。
-/
def determinantalChartPureTransformEquiv (h : (ι → R) →ₗ[R] M)
    (f : R) (n : ℕ) (hh : h.comp g = f ^ n • LinearMap.id)
    (hf : f ∈ nonZeroDivisors R) :
    let I := determinantalCenter g
    let a := determinantalCenterGenerator g m
    letI : Algebra R (BlowupChartRing I a) := (chartBaseMap I a).toAlgebra
    modulePureTransform (chartBaseMap I a f) (BlowupChartRing I a ⊗[R] M) ≃ₗ[
      BlowupChartRing I a] (ι → BlowupChartRing I a) := by
  let I := determinantalCenter g
  let a := determinantalCenterGenerator g m
  let C := BlowupChartRing I a
  letI : Algebra R C := (chartBaseMap I a).toAlgebra
  have hreg : IsSMulRegular (ι → C) (algebraMap R C f) := by
    intro x y hxy
    funext i
    apply (isRegular_iff_mem_nonZeroDivisors.mpr (chartBaseMap_nonZeroDivisors I a hf)).left
    exact congrFun hxy i
  let e₁ := modulePureTransformEquivImage (algebraMap R C f)
    (linearMapTensorToPi (C := C) g) hreg
    (fun z hz => ⟨n, by
      rw [← map_pow]
      exact linearMapTensorToPi_ker_annihilated g h (f ^ n) hh z hz⟩)
  let e₂ := LinearEquiv.ofEq _ _ (determinantalChart_tensor_range g m)
  let e₃ := LinearEquiv.ofInjective (determinantalChartColumns g m).mulVecLin
    (determinantalChartColumns_injective g m)
  exact e₁.trans (e₂.trans e₃.symm)

/--
概要：行列式生成元のチャート上の純変換は平坦。
方針：指定された有限自由加群との線形同型で平坦性を移す。
規約：KST §5、Stacks 0815、生成元チャートでの結論。
使われ方：有限階数の場合の平坦化のアフィン開被覆上の入力。
-/
theorem determinantalChartPureTransform_flat (h : (ι → R) →ₗ[R] M)
    (f : R) (n : ℕ) (hh : h.comp g = f ^ n • LinearMap.id)
    (hf : f ∈ nonZeroDivisors R) :
    let I := determinantalCenter g
    let a := determinantalCenterGenerator g m
    letI : Algebra R (BlowupChartRing I a) := (chartBaseMap I a).toAlgebra
    Module.Flat (BlowupChartRing I a)
      (modulePureTransform (chartBaseMap I a f) (BlowupChartRing I a ⊗[R] M)) := by
  let I := determinantalCenter g
  let a := determinantalCenterGenerator g m
  let : Algebra R (BlowupChartRing I a) := (chartBaseMap I a).toAlgebra
  exact Module.Flat.of_linearEquiv (determinantalChartPureTransformEquiv g m h f n hh hf)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
