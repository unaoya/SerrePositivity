module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Paths

/-! # cell path項の計算式

未知の後続語の再帰定義を展開せず、先頭一段だけを計算する。
-/
@[expose] public section
noncomputable section
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w)
variable (C : Family A D I)

lemma term_nil (x y : D) : C.term A D I [] x y = homObject A D x y := rfl

lemma term_cons (b : I) (w : List I) (x y : D) :
    C.term A D I (b :: w) x y = homObject A D x (C.source b) ⊗
      (C.generator A D I b ⊗ C.term A D I w (C.target b) y) := rfl

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
