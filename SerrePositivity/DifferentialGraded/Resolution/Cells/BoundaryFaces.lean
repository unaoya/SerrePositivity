module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.BoundaryCochain
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PathComposition

/-! # 各有限pathで一つの生成元を指定境界へ置換するcochain -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w)
variable (C : Family A D I)

/-- 先頭生成元を境界へ置き換え、左の既存Homと豊穣合成する。 -/
def replaceFirst (i : I) (w : List I) (x y : D) :
    Cochain (C.term A D I (i :: w) x y) (C.term A D I w x y) 1 :=
  (C.replaceMiddle A D I i (homObject A D x (C.source i))
      (C.term A D I w (C.target i) y)).comp
    (Cochain.ofHom
      ((α_ (homObject A D x (C.source i)) (homObject A D (C.source i) (C.target i))
        (C.term A D I w (C.target i) y)).inv ≫
        (eComp (Complex A) x (C.source i) (C.target i) ▷ C.term A D I w (C.target i) y) ≫
        C.prependMap A D I w x (C.target i) y)) (add_zero 1)

lemma replaceFirst_closed (i : I) (w : List I) (x y : D) :
    δ 1 2 (C.replaceFirst A D I i w x y) = 0 := by
  rw [replaceFirst, δ_comp_ofHom, replaceMiddle_closed]
  exact Cochain.zero_comp _ _

/-- i番目の生成元を境界へ置換する。範囲外の添字は零。 -/
def replaceFace : ∀ (w : List I) (i : ℕ) (x y : D),
    Cochain (C.term A D I w x y) (C.term A D I (w.eraseIdx i) x y) 1
  | [], _, _, _ => 0
  | i :: w, 0, x, y => C.replaceFirst A D I i w x y
  | i :: w, j + 1, x, y =>
    (tensorLeftHom (homObject A D x (C.source i)) _ _).f 1
      ((tensorLeftHom (C.generator A D I i) _ _).f 1 (replaceFace w j (C.target i) y))

lemma replaceFace_closed (w : List I) (i : ℕ) (x y : D) :
    δ 1 2 (C.replaceFace A D I w i x y) = 0 := by
  induction w generalizing i x y with
  | nil => exact δ_zero _ _
  | cons j w ih =>
    cases i with
    | zero => exact C.replaceFirst_closed A D I j w x y
    | succ i => exact homComplexMap_closed _ 1 _ (homComplexMap_closed _ 1 _ (ih i (C.target j) y))

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
