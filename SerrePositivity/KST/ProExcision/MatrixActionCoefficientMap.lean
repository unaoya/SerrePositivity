module
public import SerrePositivity.KST.ProExcision.SimplicialIdealGroups
public import SerrePositivity.KST.ProExcision.IdealMatrixAction

/-!
# 全行列作用の係数変更に関する自然性

概要：イデアルを保つ環準同型は列群と三角ブロック群の全行列作用と可換。
方針：列は有限和の保存、ブロック群は 1+B(g−1) の保存を使う。
規約：KST Lemma 4.16 の非可換な単体環への移送。
使われ方：次数ごとの外部行列作用を単体的モノイド作用へ束ねる。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} {R' : Type v} [Ring R] [Ring R']

/-- 概要：イデアル内の列群の行列作用は係数変更に自然。
方針：各成分の有限和と積を係数準同型で移す。
規約：KST 4.16。使われ方：Q の単体的な行列作用。 -/
lemma idealMatrixAction_functorial (n : ℕ) (J : TwoSidedIdeal R) (J' : TwoSidedIdeal R')
    (f : R →+* R') (hf : ∀ x, x ∈ J → f x ∈ J')
    (M : Matrix (Fin n) (Fin n) R) (v : Multiplicative (Fin n → J)) :
    idealVectorMap J J' (Fin n) f hf (idealMatrixAction n J M v) =
      idealMatrixAction n J' (M.map f) (idealVectorMap J J' (Fin n) f hf v) := by
  change (fun i ↦ idealCoefficientAddHom J J' f hf (idealMatrixVecHom n J M v.toAdd i)) =
    idealMatrixVecHom n J' (M.map f) (fun i ↦ idealCoefficientAddHom J J' f hf (v.toAdd i))
  funext i
  apply Subtype.ext
  change f (∑ j, M i j * (v.toAdd j : R)) = ∑ j, f (M i j) * f (v.toAdd j : R)
  simp only [map_sum, map_mul]

/-- 概要：diag(M,1) の実ブロック行列は係数変更に自然。
方針：四つのブロックの成分と係数準同型の零・単位の保存を使う。
規約：KST 4.16。使われ方：実ブロック群の作用の係数自然性。 -/
lemma firstBlockMatrix_coefficient_map (n m : ℕ) (f : R →+* R') (M : Matrix (Fin n) (Fin n) R) :
    (firstBlockMatrix n m M).map f = firstBlockMatrix n m (M.map f) := by
  ext i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv : Fin n ⊕ Fin m ≃ Fin (n + m)).surjective j
  cases i <;> cases j <;>
    simp only [finSumFinEquiv_apply_left, finSumFinEquiv_apply_right, Matrix.map_apply,
      firstBlockMatrix_left_left, firstBlockMatrix_left_right, firstBlockMatrix_right_left,
      firstBlockMatrix_right_right, map_zero, Matrix.one_apply]
  all_goals split_ifs <;> simp only [map_one, map_zero]

/-- 概要：実三角ブロック群の全行列作用は係数変更に自然。
方針：1+B(g−1) の実成分に環準同型を適用して群の外延性で戻す。
規約：KST 4.16、非可逆行列・非可換環のまま証明する。
使われ方：H の単体的な外部行列モノイド作用。 -/
lemma triangularBlockMatrixAction_functorial (n m : ℕ) (J : TwoSidedIdeal R) (J' : TwoSidedIdeal R')
    (f : R →+* R') (hf : ∀ x, x ∈ J → f x ∈ J')
    (M : Matrix (Fin n) (Fin n) R) (g : triangularBlockGroup n m J) :
    triangularBlockGroupMap n m J J' f hf (triangularBlockMatrixAction n m J M g) =
      triangularBlockMatrixAction n m J' (M.map f) (triangularBlockGroupMap n m J J' f hf g) := by
  apply Subtype.ext
  apply Units.ext
  change f.mapMatrix ((triangularBlockMatrixEnd n m J M g).val :
    Matrix (Fin (n + m)) (Fin (n + m)) R) =
    ((triangularBlockMatrixEnd n m J' (M.map f) (triangularBlockGroupMap n m J J' f hf g)).val :
      Matrix (Fin (n + m)) (Fin (n + m)) R')
  rw [triangularBlockMatrixEnd_val, triangularBlockMatrixEnd_val, map_add, map_one,
    map_mul, map_sub, map_one, triangularBlockGroupMap_val]
  rw [show f.mapMatrix (firstBlockMatrix n m M) = firstBlockMatrix n m (M.map f) from
    firstBlockMatrix_coefficient_map n m f M]
  rfl

end SerrePositivity.KST.ProExcision
