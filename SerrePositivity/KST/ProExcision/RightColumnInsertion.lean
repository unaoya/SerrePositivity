module
public import SerrePositivity.KST.ProExcision.TriangularConjugation

/-!
# 右乗法の列と帰納段階の実埋め込み

概要：小さい群の最後の列は補助座標挿入で大きい群の最後の列になる。
方針：first n 行の不変性と最後の列の一つ右への移動を成分公式に適用する。
規約：KST Lemma 4.16 の φ の因子化、非可換な右乗法。
使われ方：C(P) 内に値を持つ帰納仮定と μ 版 A.5 の第一項を結び付ける。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
variable {R : Type u} [Ring R]

/-- 概要：最後の補助列の直前への挿入は first n 行を動かさない。
方針：挿入位置より前の succAbove の公式を使う。
規約：KST 4.16。使われ方：列の行配置の同定。 -/
lemma auxiliaryInsertion_first_rows (n m : ℕ) (i : Fin n) :
    (auxiliaryBlockIndex n m).succAbove (Fin.castAdd (m + 1) i) = Fin.castAdd (m + 2) i := by
  have h : (Fin.castAdd (m + 1) i).castSucc < auxiliaryBlockIndex n m := by
    change i.val < n + m
    omega
  rw [Fin.succAbove_of_castSucc_lt _ _ h]
  apply Fin.ext
  rfl

/-- 概要：直前への挿入は元の最後の列を新しい最後の列へ送る。
方針：指定点自身を避ける succAbove の公式を使う。
規約：KST 4.16。使われ方：右乗法の像の列の同定。 -/
lemma auxiliaryInsertion_last (n m : ℕ) :
    (auxiliaryBlockIndex n m).succAbove (Fin.last (n + m)) = Fin.last (n + m + 1) := by
  change (Fin.last (n + m)).castSucc.succAbove (Fin.last (n + m)) = _
  rw [Fin.succAbove_castSucc_self]
  rfl

/-- 概要：小さい群の右乗法は実埋め込みの後で大きい群の右乗法に等しい。
方針：1+V の実挿入の公式と行・列の添字の同定を使う。
規約：KST Lemma 4.16 の φ の小さい帰納段階への因子化。
使われ方：μ 版 A.5 の第一入力を C(P) 内の帰納仮定とする。 -/
lemma triangularInsertion_lastRightColumn (n m : ℕ) (J : TwoSidedIdeal R) (a : R) :
    (triangularBlockGroupInsertion n (m + 1) J (auxiliaryBlockIndex n m)).comp
      (lastRightColumnHom n m J a) = lastRightColumnHom n (m + 1) J a := by
  apply MonoidHom.ext
  intro v
  apply Subtype.ext
  apply Units.ext
  change matrixInsertionHom (auxiliaryBlockIndex n m)
    (1 + blockColumn (Fin.castAdd (m + 1)) (Fin.last (n + m)) (fun i ↦ (v.toAdd i : R) * a)) =
      1 + blockColumn (Fin.castAdd (m + 2)) (Fin.last (n + m + 1)) (fun i ↦ (v.toAdd i : R) * a)
  rw [matrixInsertion_one_add_blockColumn, auxiliaryInsertion_last]
  have hr : (auxiliaryBlockIndex n m).succAbove ∘ Fin.castAdd (m + 1) = Fin.castAdd (m + 2) :=
    funext (auxiliaryInsertion_first_rows n m)
  rw [hr]

end SerrePositivity.KST.ProExcision
