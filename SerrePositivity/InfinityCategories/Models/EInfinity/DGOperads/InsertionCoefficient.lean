module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Insertion

/-!
模型。文献の定義との比較は後で
# 代数の代入作用の係数自然性

概要：BM §1 の代数作用の代入を、係数複体の射に関して比較する。
方針：係数射を分割・結合子・交換を通して作用の直前へ移す。
規約：底の複体、入力位置と arity は変えない。
使われ方：E → Com などのオペラッド射に沿う代数の制限。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

variable {A : Type u} [CommRing A]

/-- 概要：代入作用は係数射に関して自然（BM §1）。
方針：係数射と各構造同型の自然性を順に適用する。
規約：arity 零も含む全入力位置。
使われ方：オペラッド射に沿う代数制限の部分合成則。 -/
@[reassoc]
lemma tensorInsertionAction_coeff {K C D : Complex A} (f : C ⟶ D)
    (m n : ℕ) (i : Fin (m + 1)) (θ : D ⊗ power K n ⟶ K) :
    (f ▷ power K (m + n)) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction K D m n i θ =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction K C m n i ((f ▷ power K n) ≫ θ) := by
  dsimp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction]
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  rw [← whisker_exchange_assoc, ← whisker_exchange_assoc,
    associator_inv_naturality_left_assoc,
    ← comp_whiskerRight_assoc, BraidedCategory.braiding_naturality_left]
  simp only [comp_whiskerRight, Category.assoc]
  rw [associator_naturality_middle_assoc]
  simp only [← whiskerLeft_comp_assoc]
  rw [← whisker_exchange_assoc, associator_inv_naturality_left_assoc]

/-- 概要：二段の代数作用は内外の係数射に関して自然（BM §1）。
方針：結合子で二つの係数射を分け、内側の係数自然性と交換則を使う。
規約：全 arity・全入力位置。
使われ方：オペラッド射の部分合成保存から代数の合成則を移す。 -/
lemma tensorInsertionComposition_coeff {K C D C' D' : Complex A}
    (f : C ⟶ C') (g : D ⟶ D') (m n : ℕ) (i : Fin (m + 1))
    (θ : D' ⊗ power K n ⟶ K) (φ : C' ⊗ power K (m + 1) ⟶ K) :
    ((f ⊗ₘ g) ▷ power K (m + n)) ≫
      (α_ C' D' (power K (m + n))).hom ≫
      (C' ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction K D' m n i θ) ≫ φ =
    (α_ C D (power K (m + n))).hom ≫
      (C ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction K D m n i ((g ▷ power K n) ≫ θ)) ≫
      (f ▷ power K (m + 1)) ≫ φ := by
  rw [tensorHom_def, comp_whiskerRight, Category.assoc,
    associator_naturality_middle_assoc, ← whiskerLeft_comp_assoc,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionAction_coeff, associator_naturality_left_assoc,
    whisker_exchange_assoc]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
