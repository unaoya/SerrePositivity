module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSubstitutionMiddle

/-!
模型。文献の定義との比較は後で
# 二つの内側係数の交換と部分合成の順序

概要：Berger–Moerdijk §1 の外側等変性で、入力交換と最後からの代入の交換を相殺する。
方針：Koszul 対称性の対合性と結合子の自然性を適用する。
規約：外側の係数の自己射も同時に許す。
使われ方：二入力への合成の外側交換を最初の部分合成の外側等変性へ帰着する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

/-- 概要：入力交換の後の逆順の代入は、交換を相殺して外側の自己射を最初の部分合成に作用させる（Berger–Moerdijk §1）。
方針：二回の内側係数の Koszul 交換を相殺し、結合子の自然性を使う。
規約：最後の因子を先に処理する既存の代入射を使う。
使われ方：二入力の全合成の外側等変性の計算を開始する。 -/
lemma tensorSubstitutionStep_swap {C U V R O : Complex A} (a : C ⟶ C)
    (f : C ⊗ U ⟶ R) (g : R ⊗ V ⟶ O) :
    (a ⊗ₘ (β_ U V).hom) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep f g =
      (α_ C U V).inv ≫ (((a ▷ U) ≫ f) ▷ V) ≫ g := by
  simp only [tensorHom_def, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep, Category.assoc]
  rw [← whiskerLeft_comp_assoc, SymmetricCategory.symmetry, whiskerLeft_id, Category.id_comp,
    associator_inv_naturality_left_assoc, ← comp_whiskerRight_assoc]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
