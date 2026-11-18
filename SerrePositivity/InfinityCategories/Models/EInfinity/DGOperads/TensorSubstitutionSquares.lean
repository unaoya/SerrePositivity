module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSubstitutionTransport

/-!
模型。文献の定義との比較は後で
# 異なる対象を結ぶ代入射の可換正方形

概要：Berger–Moerdijk §1 の部分合成の反復で、異なる arity の間の等変性を組み合わせる。
方針：各因子の射を対称性と結合子に通し、二つの合成射の可換正方形を適用する。
規約：始域・中間対象・終域はそれぞれ異なってよい。
使われ方：二ブロックの交換で arity の表記が変わる反復合成へ用いる。
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

/-- 概要：二つの代入射の可換正方形は二段のテンソル代入の可換正方形を与える（Berger–Moerdijk §1）。
方針：対称性と結合子の自然性で各因子の射を移し、二つの正方形を順に適用する。
規約：因子と中間対象の射は自己射に限らない。
使われ方：二位置への合成と残りの反復合成の外側交換を一つの等変性へ結ぶ。 -/
lemma tensorSubstitutionStep_naturality {R V L S O R₁ V₁ L₁ S₁ O₁ : Complex A}
    (f : R ⊗ L ⟶ S) (g : S ⊗ V ⟶ O)
    (f₁ : R₁ ⊗ L₁ ⟶ S₁) (g₁ : S₁ ⊗ V₁ ⟶ O₁)
    (a : R ⟶ R₁) (b : V ⟶ V₁) (c : L ⟶ L₁)
    (d : S ⟶ S₁) (e : O ⟶ O₁)
    (hf : (a ⊗ₘ c) ≫ f₁ = f ≫ d)
    (hg : (d ⊗ₘ b) ≫ g₁ = g ≫ e) :
    (a ⊗ₘ (b ⊗ₘ c)) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep f₁ g₁ =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep f g ≫ e := by
  have hb : (a ⊗ₘ (b ⊗ₘ c)) ≫ (R₁ ◁ (β_ V₁ L₁).hom) =
      (R ◁ (β_ V L).hom) ≫ (a ⊗ₘ (c ⊗ₘ b)) := by
    simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
    rw [BraidedCategory.braiding_naturality]
  have hfg : (((a ⊗ₘ c) ⊗ₘ b) ≫ (f₁ ▷ V₁)) ≫ g₁ =
      ((f ▷ V) ≫ (d ⊗ₘ b)) ≫ g₁ := by
    congr 1
    simp only [← tensorHom_id, tensorHom_comp_tensorHom, Category.comp_id,
      Category.id_comp, hf]
  simp only [Category.assoc] at hfg
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep
  rw [← Category.assoc _ _ ((α_ R₁ L₁ V₁).inv ≫ (f₁ ▷ V₁) ≫ g₁), hb]
  simp only [Category.assoc]
  rw [associator_inv_naturality_assoc, hfg, hg]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
