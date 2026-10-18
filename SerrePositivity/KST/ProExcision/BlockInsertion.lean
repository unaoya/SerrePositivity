module
public import SerrePositivity.KST.ProExcision.MatrixInsertion
public import Mathlib.Order.Fin.Basic

/-!
# 実三角ブロック群の補助座標の挿入

概要：恒等行・列を挿入すると三角条件と係数イデアルが保たれる。
方針：指定点と既存座標に場合分けし、既存成分の差と添字の順序を使う。
規約：KST Lemma 4.16 の小さい帰納段階の P の埋め込み。
使われ方：補助行を固定する実ブロック群へ帰納仮定の値域を埋め込む。
-/
@[expose] public noncomputable section
universe u
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]

/-- 概要：補助座標の挿入で元の添字の自然数値は減らない。
方針：指定点の前では不変、後では一つ増える。
規約：KST 4.16。使われ方：first n 列の零条件を保つ添字の評価。 -/
lemma insertion_index_le {N : ℕ} (p : Fin (N + 1)) (j : Fin N) :
    j.val ≤ (p.succAbove j).val := by
  unfold Fin.succAbove
  split <;> simp

/-- 概要：恒等行・列の挿入は三角ブロックの 1 からの差の条件を保つ。
方針：指定点の成分は零の差となり、既存成分では推移的な順序と添字の下界を使う。
規約：KST 4.16、非可換な係数イデアル。
使われ方：小さいブロック群から大きいブロック群への実埋め込み。 -/
lemma matrixInsertion_difference_mem_blockPattern (N n : ℕ) (J : TwoSidedIdeal R)
    (p : Fin (N + 1)) (M : Matrix (Fin N) (Fin N) R)
    (hM : M - 1 ∈ blockPatternSubring N n J) :
    matrixInsertionHom p M - 1 ∈ blockPatternSubring (N + 1) n J := by
  constructor
  · intro i j hij
    obtain ⟨i, rfl⟩ := (finSuccEquiv' p).symm.surjective i
    obtain ⟨j, rfl⟩ := (finSuccEquiv' p).symm.surjective j
    cases i with
    | none =>
      cases j <;> simp [finSuccEquiv'_symm_none, finSuccEquiv'_symm_some,
        Matrix.sub_apply, matrixInsertion_self, matrixInsertion_row, Matrix.one_apply]
    | some i =>
      cases j with
      | none =>
        simp [finSuccEquiv'_symm_none, finSuccEquiv'_symm_some,
          Matrix.sub_apply, matrixInsertion_column, Matrix.one_apply]
      | some j =>
        simp only [finSuccEquiv'_symm_some] at hij ⊢
        rw [matrixInsertion_difference_succAbove]
        apply hM.1 i j
        intro h
        apply hij
        exact ⟨Fin.strictMono_succAbove p h.1, h.2.trans (insertion_index_le p j)⟩
  · intro i j
    obtain ⟨i, rfl⟩ := (finSuccEquiv' p).symm.surjective i
    obtain ⟨j, rfl⟩ := (finSuccEquiv' p).symm.surjective j
    cases i with
    | none =>
      cases j <;> simpa [finSuccEquiv'_symm_none, finSuccEquiv'_symm_some,
        Matrix.sub_apply, matrixInsertion_self, matrixInsertion_row, Matrix.one_apply] using J.zero_mem
    | some i =>
      cases j with
      | none =>
        simpa [finSuccEquiv'_symm_none, finSuccEquiv'_symm_some,
          Matrix.sub_apply, matrixInsertion_column, Matrix.one_apply] using J.zero_mem
      | some j =>
        simp only [finSuccEquiv'_symm_some]
        rw [matrixInsertion_difference_succAbove]
        exact hM.2 i j

/-- 概要：恒等行・列を挿入する実三角ブロック群の準同型。
方針：行列単位の挿入を制限し、単位と逆の両方の差が部分環に入ることを使う。
規約：KST Lemma 4.16、P の小さいブロック群の埋め込み。
使われ方：帰納仮定の C(P) 内のホモトピーを大きい群へ移す。 -/
def triangularBlockGroupInsertion (n m : ℕ) (J : TwoSidedIdeal R) (p : Fin (n + m + 1)) :
    triangularBlockGroup n m J →* triangularBlockGroup n (m + 1) J where
  toFun M := ⟨matrixInsertionUnits p M.val, by
    constructor
    · exact matrixInsertion_difference_mem_blockPattern (n + m) n J p _ M.property.1
    · exact matrixInsertion_difference_mem_blockPattern (n + m) n J p _ M.property.2⟩
  map_one' := by apply Subtype.ext; exact map_one (matrixInsertionUnits p)
  map_mul' M N := by apply Subtype.ext; exact map_mul (matrixInsertionUnits p) M.val N.val

end SerrePositivity.KST.ProExcision
