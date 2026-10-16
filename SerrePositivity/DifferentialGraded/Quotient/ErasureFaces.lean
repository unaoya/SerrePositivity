module
public import SerrePositivity.DifferentialGraded.Quotient.EpsilonTensor
public import SerrePositivity.DifferentialGraded.Quotient.PathComposition

/-! # 有限pathの各収縮記号を消すcochain

εを消した後、隣接する元のHomを豊穣合成する。後方のεへは全次数tensor写像で進むので、
先行するHomの次数とεの次数−1に由来するKoszul符号が保たれる。
ここでは内部微分に関する閉性を証明し、消去項の和の二乗零は後続で扱う。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

/-- 先頭のεを消し、隣り合うHomを合成する次数+1のcochain。 -/
def eraseFirst {S : Set D} (b : S) (w : Word S) (x y : D) :
    Cochain (term A D (b :: w) x y) (term A D w x y) 1 :=
  (eraseMiddle A (homObject A D x b.val) (term A D w b.val y)).comp
    (Cochain.ofHom (prependMap A D w x b.val y)) (add_zero 1)

lemma eraseFirst_closed {S : Set D} (b : S) (w : Word S) (x y : D) :
    δ 1 2 (eraseFirst A D b w x y) = 0 := by
  rw [eraseFirst, δ_comp_ofHom, eraseMiddle_closed]
  exact Cochain.zero_comp _ _

/-- i番目のεを消す。範囲外の添字は零とする。 -/
def eraseFace {S : Set D} : ∀ (w : Word S) (i : ℕ) (x y : D),
    Cochain (term A D w x y) (term A D (w.eraseIdx i) x y) 1
  | [], _, _, _ => 0
  | b :: w, 0, x, y => eraseFirst A D b w x y
  | b :: w, i + 1, x, y =>
    (tensorLeftHom (homObject A D x b.val)
      (epsilonComplex A ⊗ term A D w b.val y)
      (epsilonComplex A ⊗ term A D (w.eraseIdx i) b.val y)).f 1
      ((tensorLeftHom (epsilonComplex A) (term A D w b.val y)
        (term A D (w.eraseIdx i) b.val y)).f 1 (eraseFace w i b.val y))

@[simp] lemma eraseFace_nil (S : Set D) (i : ℕ) (x y : D) :
    eraseFace A D ([] : Word S) i x y = 0 := rfl

@[simp] lemma eraseFace_zero {S : Set D} (b : S) (w : Word S) (x y : D) :
    eraseFace A D (b :: w) 0 x y = eraseFirst A D b w x y := rfl

/-- 各ε消去は内部微分と反交換する。 -/
lemma eraseFace_closed {S : Set D} (w : Word S) (i : ℕ) (x y : D) :
    δ 1 2 (eraseFace A D w i x y) = 0 := by
  induction w generalizing i x y with
  | nil => simp only [eraseFace, δ_zero]
  | cons b w ih =>
    cases i with
    | zero => exact eraseFirst_closed A D b w x y
    | succ i =>
      exact homComplexMap_closed _ 1 _ (homComplexMap_closed _ 1 _ (ih i b.val y))

end SerrePositivity.DifferentialGraded.DGQuotient
