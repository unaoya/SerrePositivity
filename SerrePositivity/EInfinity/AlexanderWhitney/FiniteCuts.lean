module

public import SerrePositivity.EInfinity.AlexanderWhitney.ChainDiagonal

/-!
# AW 対角の有限切断和

概要：Berger–Fresse §1.1.4 の AW 対角を切断座標 0,…,n の有限和で表す。
方針：次数分割の添字と有限順序の全単射で添字を替える。
規約：前半の次数を r、後半の次数を n−r とする。
使われ方：二つの AW 対角のテンソルを独立な二つの切断座標で展開する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.AlexanderWhitney

open CategoryTheory MonoidalCategory HomologicalComplex

variable (A : Type u) [CommRing A]

local instance (n : ℕ) : Finite {i : ℕ × ℕ // i.1 + i.2 = n} :=
  inferInstanceAs (Finite ((fun i : ℕ × ℕ => i.1 + i.2) ⁻¹' {n}))

local instance (n : ℕ) : Fintype {i : ℕ × ℕ // i.1 + i.2 = n} := Fintype.ofFinite _

/-- 概要：切断座標と次数分割の全単射（BF §1.1.4）。
方針：r を (r,n−r) へ送り、第一座標を逆写像にする。
規約：始端・終端の切断を含む。
使われ方：AW の有限和の添字替え。 -/
def cutDegreeEquiv (n : ℕ) : Fin (n + 1) ≃ {i : ℕ × ℕ // i.1 + i.2 = n} where
  toFun r := ⟨(r.val, n - r.val), by omega⟩
  invFun i := ⟨i.val.1, by have hi := i.property; omega⟩
  left_inv _ := rfl
  right_inv i := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hi := i.property
      dsimp at hi ⊢
      omega

/-- 概要：AW 対角の全次数の射は切断座標の有限和（BF §1.1.4）。
方針：次数分割の和を全単射で添字付け直す。
規約：出力は既存のテンソル複体の n 次。
使われ方：shuffle の余代数射性の二つの入力の AW 対角。 -/
lemma diagonal_f_eq_sum_cuts (X : SSet.{0}) (n : ℕ) :
    (diagonal A X).f n = ∑ r : Fin (n + 1),
      component A X n r.val (n - r.val) (by omega) ≫
        ιTensorObj (chains A X) (chains A X) r.val (n - r.val) n (by omega) := by
  change diagonalDegree A X n = _
  rw [diagonalDegree_eq_sum]
  symm
  apply Fintype.sum_equiv (cutDegreeEquiv n)
  intro r
  rfl

end SerrePositivity.EInfinity.AlexanderWhitney
