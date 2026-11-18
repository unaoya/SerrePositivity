module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CoInsertionNaturality

/-!
模型。文献の定義との比較は後で
# 余演算の部分合成と係数の自然性

概要：Berger–Fresse §3.1 の外側・内側の余演算の合成を二つの係数について比較する。
方針：外側を先に適用するための交換と、指定出力への代入の自然性を組み合わせる。
規約：外側の出力数は m+1、内側の出力数は n。
使われ方：オペラッド射に沿う余代数構造の制限の合成則を証明する。
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

/-- 概要：二つの余演算の指定出力での合成（BF §3.1）。
方針：内側の係数を前へ出し、外側の余演算の後に内側を適用する。
規約：始域の係数の順序は外側・内側である。
使われ方：余代数の部分合成則の右辺をまとめる。 -/
def tensorCoComposition (K C D : Complex A) (m n : ℕ) (i : Fin (m + 1))
    (θ : C ⊗ K ⟶ power K (m + 1)) (ψ : D ⊗ K ⟶ power K n) :
    (C ⊗ D) ⊗ K ⟶ power K (m + n) :=
  ((β_ C D).hom ▷ K) ≫ (α_ D C K).hom ≫ (D ◁ θ) ≫
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorCoInsertionAction K D m n i ψ

/-- 概要：余演算の合成は両係数について自然（BF §3.1）。
方針：交換と結合子の自然性で係数射を通し、代入の係数自然性を使う。
規約：外側と内側の係数射は独立でよい。
使われ方：余代数の制限の部分合成則に用いる。 -/
lemma tensorCoComposition_coeff {K C C' D D' : Complex A}
    (f : C ⟶ C') (g : D ⟶ D') (m n : ℕ) (i : Fin (m + 1))
    (θ : C' ⊗ K ⟶ power K (m + 1)) (ψ : D' ⊗ K ⟶ power K n) :
    ((f ⊗ₘ g) ▷ K) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorCoComposition K C' D' m n i θ ψ =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorCoComposition K C D m n i ((f ▷ K) ≫ θ) ((g ▷ K) ≫ ψ) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorCoComposition]
  rw [← comp_whiskerRight_assoc, BraidedCategory.braiding_naturality]
  simp only [comp_whiskerRight, tensorHom_def, Category.assoc]
  rw [associator_naturality_middle_assoc, associator_naturality_left_assoc]
  rw [← whisker_exchange_assoc, ← whisker_exchange_assoc,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorCoInsertionAction_coeff]
  simp only [whiskerLeft_comp, Category.assoc]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
