module
public import SerrePositivity.DifferentialGraded.Quotient.PrependHomNaturality

/-! # 後方ε消去とprependMapの可換式 -/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.DifferentialGraded.DGQuotient
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D]
attribute [local irreducible] eraseFace

/-- prependMapは先頭εより後のε消去と可換する。 -/
lemma prependMap_eraseFace_succ {S : Set D} (c : S) (w : Word S) (i : ℕ) (x y z : D) :
    (Cochain.ofHom (prependMap A D (c :: w) x y z)).comp
      (eraseFace A D (c :: w) (i + 1) x z) (zero_add 1) =
    ((tensorLeftHom (homObject A D x y) (term A D (c :: w) y z)
      (term A D ((c :: w).eraseIdx (i + 1)) y z)).f 1
        (eraseFace A D (c :: w) (i + 1) y z)).comp
      (Cochain.ofHom (prependMap A D ((c :: w).eraseIdx (i + 1)) x y z)) (add_zero 1) := by
  have h := congrArg (fun t : homComplex A (term A D w c.val z)
      (term A D (w.eraseIdx i) c.val z) ⟶
      homComplex A (homObject A D x y ⊗ term A D (c :: w) y z)
        (term A D (c :: w.eraseIdx i) x z) => t.f 1 (eraseFace A D w i c.val z))
    (prependMap_suffix_hom A D c w (w.eraseIdx i) x y z)
  simp only [chain_comp_apply, homPostcompose_apply] at h
  rw [eraseFace_cons_succ, eraseFace_cons_succ]
  exact h.symm

end SerrePositivity.DifferentialGraded.DGQuotient
