module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSubstitutionUnit

/-!
模型。文献の定義との比較は後で
# 空の後半を持つテンソル代入

概要：Berger–Moerdijk §1 の入力ブロックの分解で、空の後半の代入を相殺する。
方針：テンソル単位との braiding を単位子へ直し、結合子の整合性を使う。
規約：後半の演算族はテンソル単位で表す。
使われ方：反復合成の二ブロックへの分解の空の後半の場合に用いる。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.BraidedCategory
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：空の後半の代入は右単位子の逆射と相殺される（Berger–Moerdijk §1）。
方針：空の後半との交換を左単位子へ直し、結合子と右単位子を相殺する。
規約：空の族の後に任意の係数射 a を適用してよい。
使われ方：後半のない二ブロックの合成を前半だけの合成へ簡約する。 -/
lemma tensorSubstitutionStep_empty_tail {R S V O : Complex A}
    (a : R ⟶ S) (g : S ⊗ V ⟶ O) :
    (R ◁ (ρ_ V).inv) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep ((ρ_ R).hom ≫ a) g = (a ▷ V) ≫ g := by
  have hc : (R ◁ (λ_ V).inv) ≫ (α_ R (𝟙_ (Complex A)) V).inv ≫
      ((ρ_ R).hom ▷ V) = 𝟙 (R ⊗ V) := by monoidal
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep
  rw [← whiskerLeft_comp_assoc, rightUnitor_inv_braiding]
  simp only [comp_whiskerRight, Category.assoc]
  rw [reassoc_of% hc]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
