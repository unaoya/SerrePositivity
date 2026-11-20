module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.RegularMinorAnnihilation
public import SerrePositivity.AlgebraicGeometry.FreeModuleRowPartition

/-!
概要：KST §5、Stacks 0810 の正規化したピボット関係式の像への核の包含。
方針：行を分解して補成分射影を作り、正則ピボットによる全関係式の消去を使う。
規約：元の表示の対象は保持し、正規化行列の等式を明示する。
使われ方：純変換と残る自由成分との実同型に必要な核の包含。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped Matrix

set_option backward.isDefEq.respectTransparency false in
/--
概要：正則な共通因子で割った随伴行列の関係式はピボットとの正規化等式を満たす。
方針：随伴行列と元の行列の積を使い、正則な共通因子を各成分で消す。
規約：KST §5、Stacks 0810, Lemma 38.30.2、可逆なのは行列式の単元因子だけ。
使われ方：正規化した擬関係式のグラフへ表示の核を入れる。
-/
theorem normalizedAdjugate_mul_pivot
    {R ι κ : Type*} [CommRing R] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (B C : Matrix κ ι R) (d : R) (hd : IsRegular d) (u : Rˣ)
    (hdet : A.det = d * (u : R)) (hBC : B * A.adjugate = d • C) :
    C * A = (u : R) • B := by
  have h := congrArg (fun T : Matrix κ ι R => T * A) hBC
  rw [Matrix.mul_assoc, Matrix.adjugate_mul, hdet, Matrix.mul_smul, Matrix.mul_one,
    Matrix.smul_mul] at h
  ext i j
  apply hd.left
  have hij := congrArg (fun T : Matrix κ ι R => T i j) h
  simpa only [Matrix.smul_apply, smul_eq_mul, mul_assoc] using hij.symm

set_option backward.isDefEq.respectTransparency false in
/--
概要：正則ピボットと正規化した関係式の下で、表示の核は正規化グラフの像に含まれる。
方針：補成分射影がピボット列を消すことを示し、全関係式へ拡張してグラフの元を復元する。
規約：KST §5、Stacks 0810, Lemma 38.30.2、核全体を生成する実際の行列を入力する。
使われ方：境界ねじれを除いた後の純変換の自由性。
-/
theorem kernel_le_regularMinorGraph
    {R M m n : Type*} [CommRing R] [AddCommGroup M] [Module R M] [Finite m] {k : ℕ}
    (H : Matrix m n R) (r : Fin k → m) (hr : Function.Injective r) (c : Fin k → n)
    (hd : IsRegular (H.submatrix r c).det) (hzero : matrixMinorIdeal H (k + 1) = ⊥)
    (q : (m → R) →ₗ[R] M)
    (hH : Submodule.span R (Set.range H.col) = LinearMap.ker q)
    (u : Rˣ) (C : Matrix {i : m // i ∉ Set.range r} (Fin k) R)
    (hCA : C * (H.submatrix r c) = (u : R) • (H.submatrix Subtype.val c)) :
    let E := rowPartitionLinearEquiv r hr R
    LinearMap.ker (q.comp E.symm.toLinearMap) ≤
      LinearMap.range ((((u : R) • LinearMap.id) : (Fin k → R) →ₗ[R] (Fin k → R)).prod
        C.mulVecLin) := by
  classical
  dsimp only
  let K := {i : m // i ∉ Set.range r}
  let E := rowPartitionLinearEquiv r hr R
  let A := H.submatrix r c
  let B := H.submatrix (Subtype.val : K → m) c
  let D := H.submatrix id c
  let π : ((Fin k → R) × (K → R)) →ₗ[R] (K → R) :=
    LinearMap.snd R _ _ - C.mulVecLin.comp ((↑u⁻¹ : R) • LinearMap.fst R _ _)
  have hprod : E.toLinearMap.comp D.mulVecLin = A.mulVecLin.prod B.mulVecLin :=
    rowPartitionLinearEquiv_comp_mulVecLin r hr R D
  have hπ : (π.comp E.toLinearMap).comp D.mulVecLin = 0 := by
    change π.comp (E.toLinearMap.comp D.mulVecLin) = 0
    rw [hprod]
    apply LinearMap.ext
    intro x
    change B *ᵥ x - C *ᵥ ((↑u⁻¹ : R) • (A *ᵥ x)) = 0
    rw [Matrix.mulVec_smul, Matrix.mulVec_mulVec, hCA, Matrix.smul_mulVec]
    simp [B, smul_smul]
  have hker := kernel_le_ker_of_regular_minor_selectedColumns H r c hd hzero q hH
    (π.comp E.toLinearMap) hπ
  intro z hz
  have hx : E.symm z ∈ LinearMap.ker q := hz
  have hzπ : π z = 0 := by
    have h := hker hx
    change π (E (E.symm z)) = 0 at h
    simpa only [E.apply_symm_apply] using h
  refine ⟨(↑u⁻¹ : R) • z.1, ?_⟩
  apply Prod.ext
  · change (u : R) • ((↑u⁻¹ : R) • z.1) = z.1
    simp [smul_smul]
  · change C *ᵥ ((↑u⁻¹ : R) • z.1) = z.2
    change z.2 - C *ᵥ ((↑u⁻¹ : R) • z.1) = 0 at hzπ
    exact (sub_eq_zero.mp hzπ).symm

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
