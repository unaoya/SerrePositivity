module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.BoundaryHeadInterchange

/-! # 終域のpathも保持した二重境界置換の反交換 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w)
variable (C : Family A D I)

lemma replaceFace_succ_comp (b : I) (w : List I) (i j : ℕ) (x y : D) :
    (C.replaceFace A D I (b :: w) (i + 1) x y).comp
      (C.replaceFace A D I ((b :: w).eraseIdx (i + 1)) (j + 1) x y)
      (show (1 : ℤ) + 1 = 2 by omega) =
    (tensorLeftHom (homObject A D x (C.source b)) _ _).f 2
      ((tensorLeftHom (C.generator A D I b) _ _).f 2
        ((C.replaceFace A D I w i (C.target b) y).comp
          (C.replaceFace A D I (w.eraseIdx i) j (C.target b) y) (by omega))) := by
  change (((tensorLeftHom (homObject A D x (C.source b)) _ _).f 1
      ((tensorLeftHom (C.generator A D I b) _ _).f 1
        (C.replaceFace A D I w i (C.target b) y))).comp
    ((tensorLeftHom (homObject A D x (C.source b)) _ _).f 1
      ((tensorLeftHom (C.generator A D I b) _ _).f 1
        (C.replaceFace A D I (w.eraseIdx i) j (C.target b) y))) (by omega)) = _
  rw [← tensorLeftHom_cochain_comp, ← tensorLeftHom_cochain_comp]

def DoubleFace (w : List I) (x y : D) :=
  Σ z : List I, Cochain (C.term A D I w x y) (C.term A D I z x y) 2

def doubleFace (w : List I) (i j : ℕ) (x y : D) : C.DoubleFace A D I w x y :=
  ⟨(w.eraseIdx i).eraseIdx j,
    (C.replaceFace A D I w i x y).comp (C.replaceFace A D I (w.eraseIdx i) j x y) (by omega)⟩

def negateDoubleFace {w : List I} {x y : D} :
    C.DoubleFace A D I w x y → C.DoubleFace A D I w x y
  | ⟨z, f⟩ => ⟨z, -f⟩

def prefixDoubleFace (b : I) (w : List I) (x y : D) :
    C.DoubleFace A D I w (C.target b) y → C.DoubleFace A D I (b :: w) x y
  | ⟨z, f⟩ => ⟨b :: z, (tensorLeftHom (homObject A D x (C.source b)) _ _).f 2
      ((tensorLeftHom (C.generator A D I b) _ _).f 2 f)⟩

lemma prefixDoubleFace_negate (b : I) (w : List I) (x y : D)
    (f : C.DoubleFace A D I w (C.target b) y) :
    C.prefixDoubleFace A D I b w x y (C.negateDoubleFace A D I f) =
      C.negateDoubleFace A D I (C.prefixDoubleFace A D I b w x y f) := by
  rcases f with ⟨z, f⟩
  simp only [prefixDoubleFace, negateDoubleFace, map_neg]

lemma doubleFace_cons_succ (b : I) (w : List I) (i j : ℕ) (x y : D) :
    C.doubleFace A D I (b :: w) (i + 1) (j + 1) x y =
      C.prefixDoubleFace A D I b w x y (C.doubleFace A D I w i j (C.target b) y) := by
  exact congrArg (fun f => (⟨b :: (w.eraseIdx i).eraseIdx j, f⟩ :
    C.DoubleFace A D I (b :: w) x y)) (C.replaceFace_succ_comp A D I b w i j x y)

lemma doubleFace_cons_zero (b : I) (w : List I) (j : ℕ) (x y : D) :
    C.doubleFace A D I (b :: w) 0 j x y =
      C.negateDoubleFace A D I (C.doubleFace A D I (b :: w) (j + 1) 0 x y) := by
  exact congrArg (fun f => (⟨w.eraseIdx j, f⟩ : C.DoubleFace A D I (b :: w) x y))
    (C.replaceFirst_face_anticommute A D I b w j x y)

lemma doubleFace_swap_of_le (w : List I) (i j : ℕ) (hij : i ≤ j) (x y : D) :
    C.doubleFace A D I w i j x y =
      C.negateDoubleFace A D I (C.doubleFace A D I w (j + 1) i x y) := by
  induction w generalizing i j x y with
  | nil => simp only [doubleFace, List.eraseIdx_nil, replaceFace_nil,
      Cochain.zero_comp, negateDoubleFace, neg_zero]
  | cons b w ih =>
    cases i with
    | zero => exact C.doubleFace_cons_zero A D I b w j x y
    | succ i =>
      cases j with
      | zero => omega
      | succ j =>
        rw [doubleFace_cons_succ, doubleFace_cons_succ, ← prefixDoubleFace_negate]
        exact congrArg (C.prefixDoubleFace A D I b w x y) (ih i j (by omega) (C.target b) y)

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
