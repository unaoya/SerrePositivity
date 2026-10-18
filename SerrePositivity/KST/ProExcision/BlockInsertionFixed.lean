module
public import SerrePositivity.KST.ProExcision.BlockInsertion

/-!
# 帰納段階のブロック埋め込みの固定行・列

概要：挿入された補助行は恒等行であり、既存の固定列も固定される。
方針：挿入の実成分の公式に全ての添字を帰着する。
規約：KST Lemma 4.16 の μ:P×Q→H の第一因子。
使われ方：P の全体と ψ(Q) の可換性を実ブロック埋め込みから導く。
-/
@[expose] public noncomputable section
universe u v
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]

/-- 概要：挿入した補助行は恒等行列の行。
方針：指定点と既存座標に場合分けする。
規約：KST 4.16。使われ方：P の埋め込みの固定行条件。 -/
lemma matrixInsertion_fixed_row {N : ℕ} (p : Fin (N + 1))
    (M : Matrix (Fin N) (Fin N) R) (j : Fin (N + 1)) :
    matrixInsertionHom p M p j = (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) R) p j := by
  obtain ⟨j, rfl⟩ := (finSuccEquiv' p).symm.surjective j
  cases j <;> simp [finSuccEquiv'_symm_none, finSuccEquiv'_symm_some,
    matrixInsertion_self, matrixInsertion_row, Matrix.one_apply]

/-- 概要：既存の恒等列は補助座標を挿入しても恒等列。
方針：元の成分と交差成分の公式を使う。
規約：KST 4.16。使われ方：P の埋め込みの first n 列条件。 -/
lemma matrixInsertion_fixed_column {N : ℕ} (p : Fin (N + 1))
    (M : Matrix (Fin N) (Fin N) R) (j : Fin N)
    (hj : ∀ i, M i j = (1 : Matrix (Fin N) (Fin N) R) i j) (i : Fin (N + 1)) :
    matrixInsertionHom p M i (p.succAbove j) =
      (1 : Matrix (Fin (N + 1)) (Fin (N + 1)) R) i (p.succAbove j) := by
  obtain ⟨i, rfl⟩ := (finSuccEquiv' p).symm.surjective i
  cases i <;> simp [finSuccEquiv'_symm_none, finSuccEquiv'_symm_some,
    matrixInsertion_row, matrixInsertion_succAbove, hj, Matrix.one_apply]

/-- 概要：三角ブロック群の挿入は補助列と可換な固定ブロック群に値を持つ。
方針：first n 列の固定性と挿入行の固定性を束ねる。
規約：KST 4.16、P の実埋め込み、係数環の可換性は不要。
使われ方：μ 版 A.5 の第一因子を具体的な実群準同型として与える。 -/
def triangularBlockInsertionFixedHom {ι : Type v} (n m : ℕ) (J : TwoSidedIdeal R)
    (r : ι → Fin (n + m)) (hr : ∀ k, (r k).val < n) (p : Fin (n + m + 1)) :
    triangularBlockGroup n m J →* fixedBlockSubgroup (R := R) (p.succAbove ∘ r) p where
  toFun M := ⟨matrixInsertionUnits p M.val, by
    constructor
    · intro k i
      exact matrixInsertion_fixed_column (R := R) p (M.val : Matrix (Fin (n + m)) (Fin (n + m)) R) (r k)
        (fun j ↦ triangularBlockGroup_fixed_column n m J M (r k) (hr k) j) i
    · exact matrixInsertion_fixed_row (R := R) p (M.val : Matrix (Fin (n + m)) (Fin (n + m)) R)⟩
  map_one' := by apply Subtype.ext; exact map_one (matrixInsertionUnits p)
  map_mul' M N := by apply Subtype.ext; exact map_mul (matrixInsertionUnits p) M.val N.val

end SerrePositivity.KST.ProExcision
