module

public import SerrePositivity.AlgebraicGeometry.MinorPivotFactorization
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.Algebra.Ring.NonZeroDivisors

/-!
概要：KST §5、Stacks 0810 の正則なピボットと全関係式の消去。
方針：正則な行列式を可逆化し、可逆ピボットによる因子分解の等式を単射性で戻す。
規約：基礎環の整域性は仮定せず、選んだ行列式の正則性を使う。
使われ方：純変換の自由性に必要な実際の関係式の核の包含を証明する。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped Matrix

set_option backward.isDefEq.respectTransparency false in
/--
概要：正則なピボット列を消す行列は次次数の小行列式の消滅の下で全ての列を消す。
方針：行列式を可逆化して全列をピボット列で因子分解し、正則な局所化写像の単射性で戻す。
規約：KST §5、Stacks 0810, Lemma 38.30.2、元の列数の有限性は不要。
使われ方：正規化した擬関係式への補成分射影が元の表示の核を消すことを示す。
-/
theorem mul_eq_zero_of_regular_minor_selectedColumns
    {R m n κ : Type*} [CommRing R] [Fintype m] {k : ℕ}
    (H : Matrix m n R) (r : Fin k → m) (c : Fin k → n)
    (hd : IsRegular (H.submatrix r c).det)
    (hzero : matrixMinorIdeal H (k + 1) = ⊥)
    (E : Matrix κ m R) (hE : E * (H.submatrix id c) = 0) : E * H = 0 := by
  classical
  let d := (H.submatrix r c).det
  let S := Localization.Away d
  let φ := algebraMap R S
  have hφ : Function.Injective φ :=
    IsLocalization.injective S
      (Submonoid.powers_le.mpr (isRegular_iff_mem_nonZeroDivisors.mp hd))
  have hu : IsUnit ((H.map φ).submatrix r c).det := by
    change IsUnit (φ.mapMatrix (H.submatrix r c)).det
    rw [← RingHom.map_det]
    exact IsLocalization.Away.algebraMap_isUnit d
  let : Invertible ((H.map φ).submatrix r c) :=
    ((Matrix.isUnit_iff_isUnit_det _).mpr hu).invertible
  have hzeroS : matrixMinorIdeal (H.map φ) (k + 1) = ⊥ := by
    rw [← matrixMinorIdeal_map, hzero, Ideal.map_bot]
  have hfactor := eq_selectedColumns_mul_of_succ_minorIdeal_eq_bot (H.map φ) r c hzeroS
  have hES : E.map φ * ((H.map φ).submatrix id c) = 0 := by
    change E.map φ * (H.submatrix id c).map φ = 0
    rw [← Matrix.map_mul, hE]
    exact Matrix.map_zero φ (map_zero φ)
  have hprod : E.map φ * H.map φ = 0 := by
    rw [hfactor, ← Matrix.mul_assoc, hES, Matrix.zero_mul]
  ext i j
  apply hφ
  have h := congrArg (fun T : Matrix κ n S => T i j) hprod
  simpa only [← Matrix.map_mul, Matrix.map_apply, Matrix.zero_apply, map_zero] using h

set_option backward.isDefEq.respectTransparency false in
/--
概要：正則ピボット列を消す線形写像の核は、完全な関係式表示の核を含む。
方針：線形写像を実行列にし、全列の消去から列の生成する部分加群へ移す。
規約：KST §5、Stacks 0810, Lemma 38.30.2、有限性は行の集合にだけ必要。
使われ方：擬関係式の補成分射影に元の表示の核の包含を適用する。
-/
theorem kernel_le_ker_of_regular_minor_selectedColumns
    {R M m n κ : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Finite m] {k : ℕ}
    (H : Matrix m n R) (r : Fin k → m) (c : Fin k → n)
    (hd : IsRegular (H.submatrix r c).det)
    (hzero : matrixMinorIdeal H (k + 1) = ⊥)
    (q : (m → R) →ₗ[R] M)
    (hH : Submodule.span R (Set.range H.col) = LinearMap.ker q)
    (ψ : (m → R) →ₗ[R] (κ → R))
    (hψ : ψ.comp (H.submatrix id c).mulVecLin = 0) : LinearMap.ker q ≤ LinearMap.ker ψ := by
  classical
  let : Fintype m := Fintype.ofFinite m
  let E := LinearMap.toMatrix' ψ
  have hE : E * (H.submatrix id c) = 0 := by
    apply Matrix.toLin'.injective
    rw [Matrix.toLin'_mul, map_zero]
    change (Matrix.toLin' (LinearMap.toMatrix' ψ)).comp (H.submatrix id c).mulVecLin = 0
    rw [Matrix.toLin'_toMatrix']
    exact hψ
  have hprod := mul_eq_zero_of_regular_minor_selectedColumns H r c hd hzero E hE
  rw [← hH]
  apply Submodule.span_le.mpr
  rintro z ⟨j, rfl⟩
  change ψ (H.col j) = 0
  have h := congrArg (fun T : Matrix κ n R => T.col j) hprod
  rw [Matrix.col_mul_eq_mulVec_col] at h
  change (LinearMap.toMatrix' ψ) *ᵥ H.col j = 0 at h
  simpa only [LinearMap.toMatrix'_mulVec] using h

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
