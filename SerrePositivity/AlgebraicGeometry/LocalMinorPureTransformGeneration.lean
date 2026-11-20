module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.LocalMinorPivot
public import SerrePositivity.AlgebraicGeometry.FreeModuleRowPartition
public import SerrePositivity.AlgebraicGeometry.MatrixMinorIdealRestriction
public import SerrePositivity.AlgebraicGeometry.AdjugateRelationElimination

/-!
概要：KST §5、Stacks 080Z, Lemma 15.8.9 の正則単項小行列式による純変換の生成。
方針：局所環で実際のピボットを選び、行分解と随伴行列の消去を合成する。
規約：選んだ表示行列と実際の生成全射を入力し、Fitting の表示独立性は仮定しない。
使われ方：一般有限型加群の平坦化で、正則単項となった小行列式から生成元数を減らす。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
/--
概要：局所環上の関係式の小行列式イデアルが正則単項なら、純変換はピボット外の生成元で生成される。
方針：単射ピボットを選び、自由な生成元を二成分へ分解し、随伴行列で境界ねじれを除く。
規約：KST §5、Stacks 080Z, Lemma 15.8.9 の正則単項特殊形、関係式は核の一部でもよい。
使われ方：有限表示行列の選択の下での実際の純変換の生成元削減。
-/
theorem exists_pureTransform_complement_surjection_of_regular_minorIdeal
    {R M m n : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    (H : Matrix m n R) (k : ℕ) (f : R) (hf : IsRegular f)
    (q : (m → R) →ₗ[R] M) (hq : Function.Surjective q)
    (hrel : ∀ j, q (H.col j) = 0) (hI : matrixMinorIdeal H k = Ideal.span {f}) :
    ∃ r : Fin k → m, Function.Injective r ∧
      ∃ g : ({i : m // i ∉ Set.range r} → R) →ₗ[R] modulePureTransform f M,
        Function.Surjective g := by
  classical
  obtain ⟨r, c, u, hr, _, hdet⟩ := exists_injective_minor_unit_multiple H k f hf hI
  let D : Matrix m (Fin k) R := H.submatrix id c
  let A : Matrix (Fin k) (Fin k) R := H.submatrix r c
  let B : Matrix {i : m // i ∉ Set.range r} (Fin k) R := H.submatrix Subtype.val c
  let E := rowPartitionLinearEquiv r hr R
  let q' := q.comp E.symm.toLinearMap
  have hprod : E.toLinearMap.comp D.mulVecLin = A.mulVecLin.prod B.mulVecLin :=
    rowPartitionLinearEquiv_comp_mulVecLin r hr R D
  have hqD : q.comp D.mulVecLin = 0 := by
    apply LinearMap.range_le_ker_iff.mp
    rw [Matrix.range_mulVecLin]
    apply Submodule.span_le.mpr
    rintro y ⟨j, rfl⟩
    exact hrel (c j)
  have hrel' : q'.comp (A.mulVecLin.prod B.mulVecLin) = 0 := by
    rw [← hprod]
    apply LinearMap.ext
    intro x
    change q (E.symm (E (D.mulVecLin x))) = 0
    rw [E.symm_apply_apply]
    exact LinearMap.congr_fun hqD x
  have hstack : Matrix.fromRows A B = H.submatrix (rowPartitionEquiv r hr) c := by
    ext i j
    cases i <;> rfl
  have hminor : matrixMinorIdeal (Matrix.fromRows A B) k ≤ Ideal.span {f} := by
    rw [hstack]
    exact (matrixMinorIdeal_submatrix_le H _ c k).trans hI.le
  refine ⟨r, hr, ((boundaryTorsion f M).mkQ.comp q').comp (LinearMap.inr R _ _), ?_⟩
  exact minorIdeal_pureTransform_complement_surjective f u A B q'
    (hq.comp E.symm.surjective) hrel' hdet hminor

/--
概要：有限個の生成元から k 次の正則単項小行列式を除去すると、純変換は元の個数から k を引いた個数で生成される。
方針：ピボット外の全射と、行分解の有限集合の濃度の等式を使う。
規約：KST §5、Stacks 080Z, Lemma 15.8.9 の正則単項特殊形、添字の減算は自然数。
使われ方：有限型平坦化で純変換の局所生成元数を評価する。
-/
theorem exists_fin_surjection_pureTransform_of_regular_minorIdeal
    {R M m n : Type*} [CommRing R] [IsLocalRing R] [AddCommGroup M] [Module R M]
    [Fintype m] (H : Matrix m n R) (k : ℕ) (f : R) (hf : IsRegular f)
    (q : (m → R) →ₗ[R] M) (hq : Function.Surjective q)
    (hrel : ∀ j, q (H.col j) = 0) (hI : matrixMinorIdeal H k = Ideal.span {f}) :
    ∃ g : (Fin (Fintype.card m - k) → R) →ₗ[R] modulePureTransform f M,
      Function.Surjective g := by
  classical
  obtain ⟨r, hr, g, hg⟩ :=
    exists_pureTransform_complement_surjection_of_regular_minorIdeal H k f hf q hq hrel hI
  let κ := {i : m // i ∉ Set.range r}
  let : Fintype κ := Fintype.ofFinite κ
  have hcard : k + Fintype.card κ = Fintype.card m := by
    simpa only [Fintype.card_sum, Fintype.card_fin] using
      Fintype.card_congr (rowPartitionEquiv r hr)
  have heq : Fintype.card κ = Fintype.card m - k := by omega
  let e : κ ≃ Fin (Fintype.card m - k) := (Fintype.equivFin κ).trans (finCongr heq)
  exact ⟨g.comp (LinearEquiv.funCongrLeft R R e).toLinearMap,
    hg.comp (LinearEquiv.funCongrLeft R R e).surjective⟩

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
