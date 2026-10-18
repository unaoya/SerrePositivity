module
public import SerrePositivity.KST.ProExcision.ColumnCoefficientMap

/-!
# 実ブロック埋め込みと補助元の係数変更

概要：係数準同型は恒等座標の挿入と可換であり、指定元を保つと共役補助元も保つ。
方針：挿入の成分と単一成分行列の像を評価する。
規約：KST Lemma 4.16 の (I,a) に関する関手性。
使われ方：μ の自然性と A.6 の係数変更の接続。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u v
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} {R' : Type v} [Ring R] [Ring R']

/-- 概要：実行列の補助恒等座標の挿入は係数準同型に自然。
方針：指定点と既存座標の四場合で成分を比較する。
規約：KST 4.16。使われ方：小さいブロック群の埋め込みの係数自然性。 -/
lemma matrixInsertion_coefficient_map {N : ℕ} (p : Fin (N + 1))
    (f : R →+* R') (A : Matrix (Fin N) (Fin N) R) :
    (matrixInsertionHom p A).map f = matrixInsertionHom p (A.map f) := by
  ext i j
  obtain ⟨i, rfl⟩ := (finSuccEquiv' p).symm.surjective i
  obtain ⟨j, rfl⟩ := (finSuccEquiv' p).symm.surjective j
  cases i <;> cases j <;>
    simp [finSuccEquiv'_symm_none, finSuccEquiv'_symm_some, Matrix.map_apply,
      matrixInsertion_self, matrixInsertion_row, matrixInsertion_column, matrixInsertion_succAbove]

/-- 概要：実三角ブロック群の挿入は係数イデアルの写像に自然。
方針：単位と部分群の外延性から実行列の挿入の自然性を使う。
規約：KST 4.16。使われ方：μ の第一因子の係数自然性。 -/
lemma triangularBlockInsertion_functorial (n m : ℕ) (J : TwoSidedIdeal R) (J' : TwoSidedIdeal R')
    (f : R →+* R') (hf : ∀ x, x ∈ J → f x ∈ J') (p : Fin (n + m + 1))
    (g : triangularBlockGroup n m J) :
    triangularBlockGroupInsertion n m J' p (triangularBlockGroupMap n m J J' f hf g) =
      triangularBlockGroupMap n (m + 1) J J' f hf (triangularBlockGroupInsertion n m J p g) := by
  apply Subtype.ext
  apply Units.ext
  change matrixInsertionHom p ((g.val : Matrix (Fin (n + m)) (Fin (n + m)) R).map f) =
    (matrixInsertionHom p (g.val : Matrix (Fin (n + m)) (Fin (n + m)) R)).map f
  exact (matrixInsertion_coefficient_map p f _).symm

/-- 概要：指定元を保つ係数写像は実補助元 u を保つ。
方針：単位の値の係数写像を、1 と単一成分行列の像へ分ける。
規約：KST Lemma 4.16 と A.6 の (I,a) の関手性。
使われ方：共役ホモトピーの係数変更。 -/
lemma auxiliaryBlockUnit_functorial (n m : ℕ) (J : TwoSidedIdeal R) (J' : TwoSidedIdeal R')
    (f : R →+* R') (hf : ∀ x, x ∈ J → f x ∈ J') (a : J) (a' : J') (ha : f (a : R) = (a' : R')) :
    triangularBlockGroupMap n (m + 2) J J' f hf (auxiliaryBlockUnit n m J a) =
      auxiliaryBlockUnit n m J' a' := by
  apply Subtype.ext
  apply Units.ext
  change f.mapMatrix (1 + Matrix.single (auxiliaryBlockIndex n m) (Fin.last (n + m + 1)) (a : R)) =
    1 + Matrix.single (auxiliaryBlockIndex n m) (Fin.last (n + m + 1)) (a' : R')
  rw [map_add, map_one]
  congr 1
  ext i j
  change f ((Matrix.single (auxiliaryBlockIndex n m) (Fin.last (n + m + 1)) (a : R)) i j) =
    (Matrix.single (auxiliaryBlockIndex n m) (Fin.last (n + m + 1)) (a' : R')) i j
  rw [Matrix.single_apply, Matrix.single_apply]
  split_ifs <;> first | exact ha | exact map_zero f

end SerrePositivity.KST.ProExcision
