module
public import SerrePositivity.KST.ProExcision.ColumnMatrixAction
public import SerrePositivity.KST.ProExcision.TriangularConjugation

/-!
# 実列の群準同型の全行列に関する同変性

概要：ψ と右乗法の列 φ は構成した全行列モノイドの作用と可換。
方針：実群の作用の値 1+B(g−1) を列の行列積公式で評価する。
規約：KST Lemma 4.16 の非可換な行列同変性。中心性を使わない。
使われ方：Construction A.5 の α、β と共役比較の同変性の入力。
-/
@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.ProExcision
open scoped Matrix
variable {R : Type u} [Ring R]

/-- 概要：first n 行の実補助列は全行列の左作用に同変。
方針：実群の作用の成分から補助列の行列積に帰着する。
規約：KST 4.16、非可逆な行列 M を許す。
使われ方：ψ と最後の列の同変性。 -/
lemma idealBlockColumnHom_equivariant (n m : ℕ) (J : TwoSidedIdeal R)
    (p : Fin (n + m)) (hr : ∀ i : Fin n, Fin.castAdd m i < p) (hp : n ≤ p.val)
    (M : Matrix (Fin n) (Fin n) R) (v : Multiplicative (Fin n → J)) :
    idealBlockColumnHom n m J (Fin.castAdd m) p hr hp (idealMatrixAction n J M v) =
      triangularBlockMatrixAction n m J M (idealBlockColumnHom n m J (Fin.castAdd m) p hr hp v) := by
  apply Subtype.ext
  apply Units.ext
  change 1 + blockColumn (Fin.castAdd m) p (M *ᵥ (fun i ↦ (v.toAdd i : R))) =
    ((triangularBlockMatrixEnd n m J M (idealBlockColumnHom n m J (Fin.castAdd m) p hr hp v)).val :
      Matrix (Fin (n + m)) (Fin (n + m)) R)
  rw [triangularBlockMatrixEnd_val]
  change 1 + blockColumn (Fin.castAdd m) p (M *ᵥ (fun i ↦ (v.toAdd i : R))) =
    1 + firstBlockMatrix n m M * (1 + blockColumn (Fin.castAdd m) p (fun i ↦ (v.toAdd i : R)) - 1)
  rw [add_sub_cancel_left, firstBlockMatrix_mul_blockColumn]

/-- 概要：最後の列の実準同型は全行列の左作用に同変。
方針：一般の実補助列の同変性を最後の列に適用する。
規約：KST Lemma 4.16 の φ の列の埋め込み。
使われ方：右乗法を前合成した φ の同変性。 -/
lemma lastBlockColumnHom_equivariant (n m : ℕ) (J : TwoSidedIdeal R)
    (M : Matrix (Fin n) (Fin n) R) (v : Multiplicative (Fin n → J)) :
    lastBlockColumnHom n m J (idealMatrixAction n J M v) =
      triangularBlockMatrixAction n (m + 1) J M (lastBlockColumnHom n m J v) :=
  idealBlockColumnHom_equivariant n (m + 1) J _ _ _ M v

/-- 概要：右乗法を最後の列に入れた φ は全行列の左作用に同変。
方針：イデアル内の右乗法の同変性と最後の列の同変性を合成する。
規約：KST Lemma 4.16 の非可換版、中心性・単射性は不要。
使われ方：A.5 の小さい群内の α と大きい群内の φ。 -/
lemma lastRightColumnHom_equivariant (n m : ℕ) (J : TwoSidedIdeal R) (a : R)
    (M : Matrix (Fin n) (Fin n) R) (v : Multiplicative (Fin n → J)) :
    lastRightColumnHom n m J a (idealMatrixAction n J M v) =
      triangularBlockMatrixAction n (m + 1) J M (lastRightColumnHom n m J a v) := by
  change lastBlockColumnHom n m J (idealVectorRightHom J (Fin n) a (idealMatrixAction n J M v)) = _
  rw [idealVectorRightHom_equivariant, lastBlockColumnHom_equivariant]
  rfl

/-- 概要：直前の補助列 ψ も全行列の左作用に同変。
方針：一般の実補助列の同変性を補助座標に適用する。
規約：KST Lemma 4.16 の ψ、非可換な H。
使われ方：A.6 の共役比較と補正後の相殺の同変性。 -/
lemma auxiliaryBlockColumnHom_equivariant (n m : ℕ) (J : TwoSidedIdeal R)
    (M : Matrix (Fin n) (Fin n) R) (v : Multiplicative (Fin n → J)) :
    auxiliaryBlockColumnHom n m J (idealMatrixAction n J M v) =
      triangularBlockMatrixAction n (m + 2) J M (auxiliaryBlockColumnHom n m J v) :=
  idealBlockColumnHom_equivariant n (m + 2) J _ _ _ M v

end SerrePositivity.KST.ProExcision
