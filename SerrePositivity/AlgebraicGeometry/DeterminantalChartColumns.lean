module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.DeterminantalCenter
public import SerrePositivity.AlgebraicGeometry.ChartCramer
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
概要：KST §5、Stacks 0815 の行列式中心の生成元チャート上の列の基底性。
方針：行列式の正則性から列の独立性を、Cramer の比から像ベクトルの生成性を得る。
規約：ここでは元の加群からの像ベクトルを扱う。
使われ方：基底変更後の像加群の自由化。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [DecidableEq ι] (g : M →ₗ[R] (ι → R)) (m : ι → M)

/--
概要：行列式生成元のチャート上に写した指定された列の行列。
方針：元の列行列の係数をチャートへ送る。
規約：KST §5、Stacks 0815、チャート元はこの列行列の行列式。
使われ方：自由な像加群の基底写像。
-/
def determinantalChartColumns : Matrix ι ι
    (BlowupChartRing (determinantalCenter g) (determinantalCenterGenerator g m)) :=
  (imageColumnMatrix g m).map
    (chartBaseMap (determinantalCenter g) (determinantalCenterGenerator g m))

/--
概要：指定した列行列のチャート上の行列式はチャート元の像。
方針：行列式が環準同型で保存されることを使う。
規約：KST §5、Stacks 0815、正則性の照合に使う等式。
使われ方：選んだ列の線形独立性。
-/
theorem determinantalChartColumns_det :
    (determinantalChartColumns g m).det =
      chartBaseMap (determinantalCenter g) (determinantalCenterGenerator g m)
        (determinantalCenterGenerator g m).val :=
  ((chartBaseMap (determinantalCenter g) (determinantalCenterGenerator g m)).map_det
    (imageColumnMatrix g m)).symm

set_option backward.isDefEq.respectTransparency false in
/--
概要：行列式チャートの指定された列の線形写像は単射。
方針：余因子行列を掛け、行列式の正則性で打ち消す。
規約：KST §5、Stacks 0815、行列自体の可逆性は要求しない。
使われ方：自由な像加群の基底写像の独立性。
-/
theorem determinantalChartColumns_injective :
    Function.Injective (determinantalChartColumns g m).mulVecLin := by
  intro x y hxy
  have h := congrArg (fun v => (determinantalChartColumns g m).adjugate.mulVec v) hxy
  change (determinantalChartColumns g m).adjugate.mulVec
      ((determinantalChartColumns g m).mulVec x) =
    (determinantalChartColumns g m).adjugate.mulVec
      ((determinantalChartColumns g m).mulVec y) at h
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.adjugate_mul,
    Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec,
    determinantalChartColumns_det] at h
  funext i
  apply (isRegular_iff_mem_nonZeroDivisors.mpr
    (chartBaseMap_mem_nonZeroDivisors (determinantalCenter g)
      (determinantalCenterGenerator g m))).left
  exact congrFun h i

/--
概要：元の加群の像ベクトルは行列式チャートの指定された列で生成される。
方針：置換列の行列式が同じ中心に入ることから Cramer の解を構成する。
規約：KST §5、Stacks 0815、任意の元 x の像を扱う。
使われ方：テンソル積上の像全体の生成性への入力。
-/
theorem determinantalChartColumns_vector_mem_range (x : M) :
    (fun i => chartBaseMap (determinantalCenter g) (determinantalCenterGenerator g m)
      (g x i)) ∈ LinearMap.range (determinantalChartColumns g m).mulVecLin := by
  refine ⟨chartCramerCoefficients (determinantalCenter g) (determinantalCenterGenerator g m)
    (imageColumnMatrix g m) (g x) (fun j => updateCol_det_mem_determinantalCenter g m j x), ?_⟩
  exact chartCramerCoefficients_solution (determinantalCenter g)
    (determinantalCenterGenerator g m) (imageColumnMatrix g m) rfl (g x)
      (fun j => updateCol_det_mem_determinantalCenter g m j x)

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
