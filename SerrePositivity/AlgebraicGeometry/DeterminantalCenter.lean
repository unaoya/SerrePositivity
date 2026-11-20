module

public import SerrePositivity.AlgebraicGeometry.GeneratorChartCover
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.Noetherian.Basic

/-!
概要：KST §5、Stacks 0815 の有限階数の加群の平坦化に使う行列式中心。
方針：像ベクトルの全ての列族の行列式でイデアルを生成する。
規約：階数零を含め、列の添字集合は任意の有限型とする。
使われ方：行列式生成元のチャート上での Cramer の計算。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

variable {R M ι : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [DecidableEq ι] (g : M →ₗ[R] (ι → R))

/--
概要：加群の列族の像ベクトルを列に持つ正方行列。
方針：行は像の成分、列は元の加群の族で指定する。
規約：KST §5、Stacks 0815、有限の同じ添字集合を行列の両側に使う。
使われ方：平坦化中心を生成する行列式。
-/
def imageColumnMatrix (m : ι → M) : Matrix ι ι R := fun i j => g (m j) i

/--
概要：全ての像の列族の行列式で生成する中心イデアル。
方針：生成集合のイデアル包を取る。
規約：KST §5、Stacks 0815、Noether 性は定義に不要。
使われ方：有限階数自由な境界外部分を持つ加群の平坦化。
-/
def determinantalCenter : Ideal R :=
  Ideal.span (Set.range (fun m : ι → M => (imageColumnMatrix g m).det))

/--
概要：像の列族の行列式を中心の実際の元として扱う。
方針：生成集合の元がイデアル包に入ることを使う。
規約：KST §5、Stacks 0815、列族を生成元の添字とする。
使われ方：行列式の blowup チャートの指定。
-/
def determinantalCenterGenerator (m : ι → M) : determinantalCenter g :=
  ⟨(imageColumnMatrix g m).det, Ideal.subset_span ⟨m, rfl⟩⟩

omit [Fintype ι] in
/--
概要：列族の一列の置換は像の行列の列置換に一致する。
方針：更新された列とそれ以外の列に分ける。
規約：KST §5、Stacks 0815、行列式の符号変更は起きない。
使われ方：Cramer の分子が同じ中心に属すること。
-/
theorem imageColumnMatrix_update (m : ι → M) (j : ι) (x : M) :
    imageColumnMatrix g (Function.update m j x) =
      (imageColumnMatrix g m).updateCol j (g x) := by
  ext i k
  by_cases hk : k = j
  · subst k
    simp [imageColumnMatrix]
  · simp [imageColumnMatrix, hk]

/--
概要：像の一列を置換した行列式も行列式中心に入る。
方針：更新した列族の行列式を生成元として使う。
規約：KST §5、Stacks 0815、置換する元は元の加群の任意の元。
使われ方：行列式生成元のチャートでの比の構成。
-/
theorem updateCol_det_mem_determinantalCenter (m : ι → M) (j : ι) (x : M) :
    ((imageColumnMatrix g m).updateCol j (g x)).det ∈ determinantalCenter g := by
  rw [← imageColumnMatrix_update]
  exact Ideal.subset_span ⟨Function.update m j x, rfl⟩

/--
概要：環の自由加群側の合成が境界の冪倍なら、行列式中心は境界の冪を含む。
方針：自由加群の標準基底を戻した列族の行列式を計算する。
規約：KST §5、Stacks 0815、指数は元の指数と階数の積。
使われ方：行列式中心の admissible 性。
-/
theorem boundary_pow_mem_determinantalCenter (h : (ι → R) →ₗ[R] M)
    (f : R) (n : ℕ) (hgh : g.comp h = f ^ n • LinearMap.id) :
    f ^ (n * Fintype.card ι) ∈ determinantalCenter g := by
  let m : ι → M := fun j => h (Pi.single j 1)
  have hm : imageColumnMatrix g m = f ^ n • (1 : Matrix ι ι R) := by
    ext i j
    have hij := congrFun (LinearMap.congr_fun hgh (Pi.single j 1)) i
    simpa [imageColumnMatrix, m, Matrix.one_apply, Pi.single_apply, eq_comm] using hij
  have hmem := (determinantalCenterGenerator g m).property
  change (imageColumnMatrix g m).det ∈ determinantalCenter g at hmem
  simpa only [hm, Matrix.det_smul, Matrix.det_one, mul_one, pow_mul] using hmem

/--
概要：行列式を指定する全チャートは行列式中心の blowup を覆う。
方針：中心の定義通りの生成族による標準被覆を使う。
規約：KST §5、Stacks 0815、列族の集合の有限性は要求しない。
使われ方：生成元チャート上の自由性からの局所平坦性。
-/
theorem iSup_determinantalCenter_charts :
    ⨆ m : ι → M, affineBlowupChart (determinantalCenter g)
      (determinantalCenterGenerator g m) = ⊤ :=
  iSup_affineBlowup_generatorCharts (determinantalCenter g)
    (determinantalCenterGenerator g) rfl

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
