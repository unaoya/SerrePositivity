module

public import SerrePositivity.EInfinity.BarrattEccles.PartialCompositionExt
public import SerrePositivity.EInfinity.BarrattEccles.ShuffleEquivariance
public import SerrePositivity.EInfinity.BarrattEccles.NormalizedRightAction
public import SerrePositivity.DifferentialGraded.Complexes.MaurerCartanCurrying

/-!
# shuffle 部分合成の複体の射としての等変性

概要：Berger–Fresse §0.10、§1.1.3 の内側・外側の等変性を複体の射の等式として証明する。
方針：負の純粋テンソルで評価し、次数同型の自然性と正規化鎖の等変性を使う。
規約：作用は complexRightAction による右作用である。
使われ方：Barratt–Eccles オペラッドの等変性のフィールドへ渡す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.BarrattEccles

open CategoryTheory MonoidalCategory HomologicalComplex
open SerrePositivity.DifferentialGraded

variable (A : Type u) [CommRing A]

/-- 概要：部分合成の複体の射は内側の右作用に関して等変である（Berger–Fresse §1.1.3）。
方針：純粋テンソルの成分で内側作用の自然性と shuffle 双線形写像の等変性を適用する。
規約：内側の置換は出力の挿入区間へ延長する。
使われ方：Barratt–Eccles オペラッドの内側等変性となる。 -/
lemma partialComposition_inner_rightAction (m n : ℕ) (i : Fin (m + 1))
    (κ : Equiv.Perm (Fin n)) :
    (complex A (m + 1) ◁ complexRightAction A n κ) ≫ partialComposition A m n i =
      partialComposition A m n i ≫
        complexRightAction A (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i κ) := by
  apply tensor_complex_hom_ext A (m + 1) n
  intro p q x y
  change (partialComposition A m n i).f (-((p + q : ℕ) : ℤ))
      ((complex A (m + 1) ◁ complexRightAction A n κ).f (-((p + q : ℕ) : ℤ))
        (ιTensorObj (complex A (m + 1)) (complex A n) (-(p : ℤ)) (-(q : ℤ))
          (-((p + q : ℕ) : ℤ)) (by omega) (x ⊗ₜ[A] y))) =
    (complexRightAction A (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i κ)).f (-((p + q : ℕ) : ℤ))
      ((partialComposition A m n i).f (-((p + q : ℕ) : ℤ))
        (ιTensorObj (complex A (m + 1)) (complex A n) (-(p : ℤ)) (-(q : ℤ))
          (-((p + q : ℕ) : ℤ)) (by omega) (x ⊗ₜ[A] y)))
  rw [SerrePositivity.DifferentialGraded.whiskerLeft_apply (complex A (m + 1))
    (complexRightAction A n κ) (-(p : ℤ)) (-(q : ℤ)) (-((p + q : ℕ) : ℤ)) (by omega) x y,
    partialComposition_neg_tmul A m n i p q, partialComposition_neg_tmul A m n i p q]
  rw [complexRightAction_normalized_apply A n q κ,
    complexRightAction_normalized_inv_apply A (m + n) (p + q) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadInnerPermutation m n i κ)]
  rw [shuffleBilinear_inner_rightAction A m n i p q κ]

/-- 概要：部分合成の複体の射は外側の右作用に関して等変である（Berger–Fresse §1.1.3）。
方針：純粋テンソルの成分で外側作用の自然性と挿入位置を移す shuffle の等変性を適用する。
規約：右作用 ρ によって作用前の挿入位置は ρ(i) へ移る。
使われ方：Barratt–Eccles オペラッドの外側等変性となる。 -/
lemma partialComposition_outer_rightAction (m n : ℕ) (i : Fin (m + 1))
    (ρ : Equiv.Perm (Fin (m + 1))) :
    (complexRightAction A (m + 1) ρ ▷ complex A n) ≫ partialComposition A m n i =
      partialComposition A m n (ρ i) ≫
        complexRightAction A (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i ρ) := by
  apply tensor_complex_hom_ext A (m + 1) n
  intro p q x y
  change (partialComposition A m n i).f (-((p + q : ℕ) : ℤ))
      ((complexRightAction A (m + 1) ρ ▷ complex A n).f (-((p + q : ℕ) : ℤ))
        (ιTensorObj (complex A (m + 1)) (complex A n) (-(p : ℤ)) (-(q : ℤ))
          (-((p + q : ℕ) : ℤ)) (by omega) (x ⊗ₜ[A] y))) =
    (complexRightAction A (m + n) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i ρ)).f (-((p + q : ℕ) : ℤ))
      ((partialComposition A m n (ρ i)).f (-((p + q : ℕ) : ℤ))
        (ιTensorObj (complex A (m + 1)) (complex A n) (-(p : ℤ)) (-(q : ℤ))
          (-((p + q : ℕ) : ℤ)) (by omega) (x ⊗ₜ[A] y)))
  rw [SerrePositivity.DifferentialGraded.whiskerRight_apply (complexRightAction A (m + 1) ρ)
    (complex A n) (-(p : ℤ)) (-(q : ℤ)) (-((p + q : ℕ) : ℤ)) (by omega) x y,
    partialComposition_neg_tmul A m n i p q, partialComposition_neg_tmul A m n (ρ i) p q]
  rw [complexRightAction_normalized_apply A (m + 1) p ρ,
    complexRightAction_normalized_inv_apply A (m + n) (p + q) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.operadOuterPermutation m n i ρ)]
  rw [shuffleBilinear_outer_rightAction A m n i p q ρ]

end SerrePositivity.EInfinity.BarrattEccles
