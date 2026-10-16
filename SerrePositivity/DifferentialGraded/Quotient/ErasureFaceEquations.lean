module
public import SerrePositivity.DifferentialGraded.Quotient.ErasureFaces

/-! # 先頭εを保つfaceの一段の再帰式

後方の再帰呼出しを展開せずに、先頭のtensor作用だけを公開する。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]

lemma eraseFace_cons_succ {S : Set D} (b : S) (w : Word S) (i : ℕ) (x y : D) :
    eraseFace A D (b :: w) (i + 1) x y =
    (tensorLeftHom (homObject A D x b.val)
      (epsilonComplex A ⊗ term A D w b.val y)
      (epsilonComplex A ⊗ term A D (w.eraseIdx i) b.val y)).f 1
      ((tensorLeftHom (epsilonComplex A) (term A D w b.val y)
        (term A D (w.eraseIdx i) b.val y)).f 1 (eraseFace A D w i b.val y)) := rfl

end SerrePositivity.DifferentialGraded.DGQuotient
