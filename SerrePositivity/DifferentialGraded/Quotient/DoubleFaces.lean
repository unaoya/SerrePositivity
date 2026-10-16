module
public import SerrePositivity.DifferentialGraded.Quotient.ErasureAdjacentInterchange
public import SerrePositivity.DifferentialGraded.Quotient.ErasureTailComposition

/-! # 終域の語を保持した二重ε消去

消去後の語とcochainを依存対で保持し、異なる消去順序の終域を同時に比較する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 終域の語付き次数2 cochain。 -/
def DoubleFace {S : Set D} (w : Word S) (x y : D) :=
  Σ z : Word S, Cochain (term A D w x y) (term A D z x y) 2

/-- 二つの位置を順に消し、終域の語も保持する。 -/
def doubleFace {S : Set D} (w : Word S) (i j : ℕ) (x y : D) : DoubleFace A D w x y :=
  ⟨(w.eraseIdx i).eraseIdx j,
    (eraseFace A D w i x y).comp (eraseFace A D (w.eraseIdx i) j x y) (by omega)⟩

/-- 終域の語を変えずcochainを負にする。 -/
def negateDoubleFace {S : Set D} {w : Word S} {x y : D} :
    DoubleFace A D w x y → DoubleFace A D w x y
  | ⟨z, f⟩ => ⟨z, -f⟩

lemma negateDoubleFace_involutive {S : Set D} {w : Word S} {x y : D}
    (f : DoubleFace A D w x y) : negateDoubleFace A D (negateDoubleFace A D f) = f := by
  rcases f with ⟨z, f⟩
  simp only [negateDoubleFace, neg_neg]

/-- 前方Homとεを残して次数2 cochainをtensorする。 -/
def prefixDoubleFace {S : Set D} (b : S) (w : Word S) (x y : D) :
    DoubleFace A D w b.val y → DoubleFace A D (b :: w) x y
  | ⟨z, f⟩ => ⟨b :: z,
      (tensorLeftHom (homObject A D x b.val) (epsilonComplex A ⊗ term A D w b.val y)
        (epsilonComplex A ⊗ term A D z b.val y)).f 2
        ((tensorLeftHom (epsilonComplex A) (term A D w b.val y)
          (term A D z b.val y)).f 2 f)⟩

lemma prefixDoubleFace_negate {S : Set D} (b : S) (w : Word S) (x y : D)
    (f : DoubleFace A D w b.val y) :
    prefixDoubleFace A D b w x y (negateDoubleFace A D f) =
      negateDoubleFace A D (prefixDoubleFace A D b w x y f) := by
  rcases f with ⟨z, f⟩
  simp only [prefixDoubleFace, negateDoubleFace, map_neg]

lemma doubleFace_cons_succ {S : Set D} (b : S) (w : Word S) (i j : ℕ) (x y : D) :
    doubleFace A D (b :: w) (i + 1) (j + 1) x y =
      prefixDoubleFace A D b w x y (doubleFace A D w i j b.val y) := by
  exact congrArg (fun f => (⟨b :: (w.eraseIdx i).eraseIdx j, f⟩ :
    DoubleFace A D (b :: w) x y)) (eraseFace_succ_comp A D b w i j x y)

lemma doubleFace_cons_zero {S : Set D} (b : S) (w : Word S) (j : ℕ) (x y : D) :
    doubleFace A D (b :: w) 0 j x y =
      negateDoubleFace A D (doubleFace A D (b :: w) (j + 1) 0 x y) := by
  exact congrArg (fun f => (⟨w.eraseIdx j, f⟩ : DoubleFace A D (b :: w) x y))
    (eraseFirst_face_anticommute A D b w j x y)

/-- 異なる二つの元の位置を消す順序の交換は、終域の語も含めて反交換する。 -/
lemma doubleFace_swap_of_le {S : Set D} (w : Word S) (i j : ℕ) (hij : i ≤ j) (x y : D) :
    doubleFace A D w i j x y =
      negateDoubleFace A D (doubleFace A D w (j + 1) i x y) := by
  induction w generalizing i j x y with
  | nil => simp only [doubleFace, List.eraseIdx_nil, eraseFace_nil,
      Cochain.zero_comp, negateDoubleFace, neg_zero]
  | cons b w ih =>
    cases i with
    | zero => exact doubleFace_cons_zero A D b w j x y
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        rw [doubleFace_cons_succ, doubleFace_cons_succ, ← prefixDoubleFace_negate]
        exact congrArg (prefixDoubleFace A D b w x y) (ih i j (by omega) b.val y)

end SerrePositivity.DifferentialGraded.DGQuotient
