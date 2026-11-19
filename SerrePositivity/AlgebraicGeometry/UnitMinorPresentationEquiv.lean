module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.MinorPivotFactorization
public import SerrePositivity.AlgebraicGeometry.FreeModuleRowPartition
public import SerrePositivity.AlgebraicGeometry.RelationPivotElimination

/-!
概要：KST §5、Stacks 0810, Lemma 38.30.2 の単元小行列式からの表示対象の実同型。
方針：次次数の消滅によるピボット列の核の生成と行分解を接続する。
規約：元の対象は固定し、補成分からの実際の線形同型を構成する。
使われ方：局所環の小行列式条件から自由性を導く。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry

/--
概要：可逆ピボットと次次数の消滅を持つ完全な表示の対象は、ピボット外の成分と実際に線形同型。
方針：全核がピボット列の像であることを証明し、可逆な成分の消去による同型を使う。
規約：KST §5、Stacks 0810, Lemma 38.30.2、行・列全体の有限性はこの構成には不要。
使われ方：小行列式の単位条件と消滅から局所自由なモデルを作る。
-/
def unitMinorPresentationComplementEquiv
    {R M m n : Type*} [CommRing R] [AddCommGroup M] [Module R M] {k : ℕ}
    (H : Matrix m n R) (r : Fin k → m) (hr : Function.Injective r) (c : Fin k → n)
    [Invertible (H.submatrix r c)]
    (q : (m → R) →ₗ[R] M) (hq : Function.Surjective q)
    (hH : Submodule.span R (Set.range H.col) = LinearMap.ker q)
    (hzero : matrixMinorIdeal H (k + 1) = ⊥) :
    ({i : m // i ∉ Set.range r} → R) ≃ₗ[R] M := by
  classical
  let D : Matrix m (Fin k) R := H.submatrix id c
  let A : Matrix (Fin k) (Fin k) R := H.submatrix r c
  let B : Matrix {i : m // i ∉ Set.range r} (Fin k) R := H.submatrix Subtype.val c
  let E := rowPartitionLinearEquiv r hr R
  let q' := q.comp E.symm.toLinearMap
  let t := A.mulVecLin.prod B.mulVecLin
  have hprod : E.toLinearMap.comp D.mulVecLin = t :=
    rowPartitionLinearEquiv_comp_mulVecLin r hr R D
  have hrange : LinearMap.range D.mulVecLin = LinearMap.ker q := by
    rw [Matrix.range_mulVecLin]
    exact (columnSpan_eq_selectedColumns_of_succ_minorIdeal_eq_bot H r c hzero).symm.trans hH
  have hker : LinearMap.ker q' = LinearMap.range t := by
    apply le_antisymm
    · intro z hz
      have hx : E.symm z ∈ LinearMap.ker q := hz
      rw [← hrange] at hx
      obtain ⟨x, hx⟩ := hx
      refine ⟨x, ?_⟩
      have h : E (D.mulVecLin x) = z := by rw [hx, E.apply_symm_apply]
      exact (LinearMap.congr_fun hprod x).symm.trans h
    · rintro z ⟨x, rfl⟩
      change q (E.symm (t x)) = 0
      have htx : E (D.mulVecLin x) = t x := LinearMap.congr_fun hprod x
      rw [← htx, E.symm_apply_apply]
      exact hrange.le ⟨x, rfl⟩
  let eA : (Fin k → R) ≃ₗ[R] (Fin k → R) := LinearEquiv.ofBijective A.mulVecLin
    ⟨Matrix.mulVec_injective_of_isUnit (isUnit_of_invertible A),
      Matrix.mulVec_surjective_of_invertible A⟩
  exact relationPivotComplementEquiv q' t eA (hq.comp E.symm.surjective)
    (LinearMap.range_le_ker_iff.mp hker.ge) hker rfl

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
