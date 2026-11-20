module

public meta import SerrePositivity.Util.DeprecatedAlias
public import SerrePositivity.AlgebraicGeometry.PureTransformPivotElimination
public import SerrePositivity.AlgebraicGeometry.MatrixMinorIdeal
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
概要：KST §5、Stacks 080Z, Lemma 15.8.9 の随伴行列による純変換の生成元消去。
方針：選んだ小行列式と随伴行列の積で、単元成分を持つ擬関係式を作る。
規約：行列式と下成分の可除性は実際の等式として入力する。
使われ方：正則単項の小行列式イデアルから生成元数の制限を導く中心的計算。
-/

@[expose] public noncomputable section
namespace SerrePositivity.AlgebraicGeometry
open scoped Matrix

variable {R M ι κ : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [DecidableEq ι]

/--
概要：下成分と随伴行列の積の係数は行置換小行列式に一致する。
方針：転置した Cramer の公式を成分ごとに使う。
規約：KST §5、Stacks 080Z, Lemma 15.8.9、行列式の可逆性は仮定しない。
使われ方：小行列式の可除性から擬関係式の係数を選ぶ。
-/
theorem mul_adjugate_entry_eq_updateRow_det
    (A : Matrix ι ι R) (B : Matrix κ ι R) (i : κ) (j : ι) :
    (B * A.adjugate) i j = (A.updateRow j (B i)).det := by
  calc
    (B * A.adjugate) i j = (A.adjugate.transpose *ᵥ B i) j := by
      simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      apply Finset.sum_congr rfl
      intro l _
      exact mul_comm _ _
    _ = (A.updateRow j (B i)).det := by
      rw [Matrix.adjugate_transpose, ← Matrix.cramer_eq_adjugate_mulVec,
        Matrix.cramer_transpose_apply]

/--
概要：境界元の単元倍となる小行列式と随伴行列の可除性から、純変換の生成元を除去する。
方針：随伴行列を関係式に合成し、境界元により消える単元成分付きの擬関係式を作る。
規約：KST §5、Stacks 080Z, Lemma 15.8.9、下成分の添字は有限とは限らない。
使われ方：局所環上の小行列式イデアルが単項となる場合の純変換の生成元数判定。
-/
theorem adjugate_pureTransform_complement_surjective (f : R) (u : Rˣ)
    (A : Matrix ι ι R) (B C : Matrix κ ι R)
    (q : ((ι → R) × (κ → R)) →ₗ[R] M) (hq : Function.Surjective q)
    (hrel : q.comp (A.mulVecLin.prod B.mulVecLin) = 0)
    (hdet : A.det = f * (u : R)) (hBC : B * A.adjugate = f • C) :
    Function.Surjective (((boundaryTorsion f M).mkQ.comp q).comp
      (LinearMap.inr R (ι → R) (κ → R))) := by
  let t : (ι → R) →ₗ[R] ((ι → R) × (κ → R)) :=
    ((u : R) • LinearMap.id).prod C.mulVecLin
  apply pureTransformPivotComplement_surjective f q t (LinearEquiv.smulOfUnit u) hq
  · intro x
    have hs : f • t x =
        (A.mulVecLin.prod B.mulVecLin) (A.adjugate *ᵥ x) := by
      apply Prod.ext
      · change f • ((u : R) • x) = A *ᵥ (A.adjugate *ᵥ x)
        rw [Matrix.mulVec_mulVec, Matrix.mul_adjugate, hdet,
          Matrix.smul_mulVec, Matrix.one_mulVec, mul_smul]
      · change f • (C *ᵥ x) = B *ᵥ (A.adjugate *ᵥ x)
        rw [Matrix.mulVec_mulVec, hBC, Matrix.smul_mulVec]
    apply (mem_boundaryTorsion_iff f M _).mpr
    refine ⟨1, ?_⟩
    rw [pow_one, ← map_smul, hs]
    exact LinearMap.congr_fun hrel _
  · rfl

/--
概要：全行置換小行列式の可除性から、純変換への残りの生成元の全射を構成する。
方針：随伴行列の積の各係数の商を選び、境界倍の擬関係式を作る。
規約：KST §5、Stacks 080Z, Lemma 15.8.9、割り算の一意性や境界の正則性は不要。
使われ方：正則単項の小行列式イデアルの局所生成元に対する実際の消去。
-/
theorem adjugate_pureTransform_complement_surjective_of_minors_dvd
    (f : R) (u : Rˣ) (A : Matrix ι ι R) (B : Matrix κ ι R)
    (q : ((ι → R) × (κ → R)) →ₗ[R] M) (hq : Function.Surjective q)
    (hrel : q.comp (A.mulVecLin.prod B.mulVecLin) = 0)
    (hdet : A.det = f * (u : R))
    (hdiv : ∀ i j, f ∣ (A.updateRow j (B i)).det) :
    Function.Surjective (((boundaryTorsion f M).mkQ.comp q).comp
      (LinearMap.inr R (ι → R) (κ → R))) := by
  choose C hC using hdiv
  have hBC : B * A.adjugate = f • (C : Matrix κ ι R) := by
    ext i j
    rw [mul_adjugate_entry_eq_updateRow_det, hC i j]
    rfl
  exact adjugate_pureTransform_complement_surjective f u A B C q hq hrel hdet hBC

set_option backward.isDefEq.respectTransparency false in
/--
概要：小行列式イデアルの単項イデアルへの包含と単元倍のピボットから、純変換の生成元を除去する。
方針：各行置換を元の行列の小行列として表し、可除性から随伴行列の消去を使う。
規約：KST §5、Stacks 080Z, Lemma 15.8.9、ピボット行を最初の Fin(n) に並べた表示。
使われ方：局所環で単項小行列式イデアルの生成元を選んだ後の生成元数判定。
-/
theorem minorIdeal_pureTransform_complement_surjective {n : ℕ}
    (f : R) (u : Rˣ) (A : Matrix (Fin n) (Fin n) R) (B : Matrix κ (Fin n) R)
    (q : ((Fin n → R) × (κ → R)) →ₗ[R] M) (hq : Function.Surjective q)
    (hrel : q.comp (A.mulVecLin.prod B.mulVecLin) = 0)
    (hdet : A.det = f * (u : R))
    (hI : matrixMinorIdeal (Matrix.fromRows A B) n ≤ Ideal.span {f}) :
    Function.Surjective (((boundaryTorsion f M).mkQ.comp q).comp
      (LinearMap.inr R (Fin n → R) (κ → R))) := by
  apply adjugate_pureTransform_complement_surjective_of_minors_dvd f u A B q hq hrel hdet
  intro i j
  apply Ideal.mem_span_singleton.mp
  apply hI
  let r : Fin n → Fin n ⊕ κ := Function.update Sum.inl j (Sum.inr i)
  have hmat : (Matrix.fromRows A B).submatrix r id = A.updateRow j (B i) := by
    ext l t
    change Sum.elim A B (r l) t = Function.update A j (B i) l t
    by_cases hl : l = j
    · subst l
      rw [Function.update_self]
      have hr : r j = Sum.inr i := Function.update_self _ _ _
      rw [hr]
      rfl
    · rw [Function.update_of_ne hl]
      have hr : r l = Sum.inl l := Function.update_of_ne hl _ _
      rw [hr]
      rfl
  rw [← hmat]
  exact det_submatrix_mem_matrixMinorIdeal _ n r id

end SerrePositivity.AlgebraicGeometry

/-! ## 移動前の名前との互換 -/

set_option linter.style.longLine false
set_option linter.auxLemma false

namespace SerrePositivity.KST.SchemeLemmas
end SerrePositivity.KST.SchemeLemmas
