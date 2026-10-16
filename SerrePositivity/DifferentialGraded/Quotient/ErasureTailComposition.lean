module
public import SerrePositivity.DifferentialGraded.Quotient.ErasureFaces
public import SerrePositivity.DifferentialGraded.Complexes.TensorCochainComposition

/-! # 先頭記号を保つ二重消去の帰納式

二つの消去位置がともに先頭より後なら、二重消去は短いpathの二重消去を
先頭Homとεで二重に左tensorしたものになる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 範囲外の位置でεを消すfaceは零である。 -/
lemma eraseFace_eq_zero_of_length_le {S : Set D} (w : Word S) (i : ℕ)
    (hi : w.length ≤ i) (x y : D) : eraseFace A D w i x y = 0 := by
  induction w generalizing i x y with
  | nil => rfl
  | cons b w ih =>
    cases i with
    | zero => simp only [List.length_cons] at hi; omega
    | succ i =>
      dsimp only [eraseFace]
      rw [ih i (by simpa only [List.length_cons, Nat.succ_le_succ_iff] using hi),
        map_zero, map_zero]

/-- 二つとも先頭より後の消去なら、合成は短いpathでの合成から得られる。 -/
lemma eraseFace_succ_comp {S : Set D} (b : S) (w : Word S) (i j : ℕ) (x y : D) :
    (eraseFace A D (b :: w) (i + 1) x y).comp
      (eraseFace A D ((b :: w).eraseIdx (i + 1)) (j + 1) x y)
      (show (1 : ℤ) + 1 = 2 by omega) =
    (tensorLeftHom (homObject A D x b.val)
      (epsilonComplex A ⊗ term A D w b.val y)
      (epsilonComplex A ⊗ term A D ((w.eraseIdx i).eraseIdx j) b.val y)).f 2
      ((tensorLeftHom (epsilonComplex A) (term A D w b.val y)
        (term A D ((w.eraseIdx i).eraseIdx j) b.val y)).f 2
          ((eraseFace A D w i b.val y).comp
            (eraseFace A D (w.eraseIdx i) j b.val y) (by omega))) := by
  change
    (((tensorLeftHom (homObject A D x b.val) _ _).f 1
      ((tensorLeftHom (epsilonComplex A) _ _).f 1 (eraseFace A D w i b.val y))).comp
      ((tensorLeftHom (homObject A D x b.val) _ _).f 1
        ((tensorLeftHom (epsilonComplex A) _ _).f 1
          (eraseFace A D (w.eraseIdx i) j b.val y))) (by omega)) = _
  rw [← tensorLeftHom_cochain_comp, ← tensorLeftHom_cochain_comp]

end SerrePositivity.DifferentialGraded.DGQuotient
