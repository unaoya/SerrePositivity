module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SubstitutionParallelCoherence

/-!
模型。文献の定義との比較は後で
# 異なる入力へのテンソル代入の反復

概要：Berger–Moerdijk §1 の異なる入力への代入の交換を、残りの入力族の代入へ拡張する。
方針：一段の交換則と残りの交換則を結合し、三因子の braiding の整合性を使う。
規約：U の係数を V と L の入力族の後へ移す。
使われ方：先頭への部分合成と後半への反復代入を交換する帰納段階に用いる。
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

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：一段の代入の交換と残りの代入の交換は、二段の代入全体の交換を与える（Berger–Moerdijk §1）。
方針：係数射を構造射へ通し、二つの交換則と四因子の交換の整合性を適用する。
規約：V は残りの入力族、L は最後に分離した入力の係数。
使われ方：オペラッドの parallel_assoc を有限族への反復代入の交換へ持ち上げる。 -/
lemma tensorSubstitutionStep_parallel {R U V L S S₁ R₁ R₂ O : Complex A}
    (f : R ⊗ U ⟶ S) (g : R ⊗ L ⟶ R₁) (h : S ⊗ L ⟶ S₁)
    (f₁ : R₁ ⊗ U ⟶ S₁) (v : S₁ ⊗ V ⟶ O) (w : R₁ ⊗ V ⟶ R₂) (f₂ : R₂ ⊗ U ⟶ O)
    (hf : (f ▷ L) ≫ h = (α_ R U L).hom ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep g f₁)
    (hv : (f₁ ▷ V) ≫ v = (α_ R₁ U V).hom ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep w f₂) :
    (f ▷ (V ⊗ L)) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep h v =
      (α_ R U (V ⊗ L)).hom ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep g w) f₂ := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep
  rw [← whisker_exchange_assoc, associator_inv_naturality_left_assoc,
    ← comp_whiskerRight_assoc, hf]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep, comp_whiskerRight, Category.assoc]
  rw [hv]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep]
  rw [associator_naturality_left_assoc, ← whisker_exchange_assoc,
    associator_inv_naturality_left_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.substitutionParallel_four_assoc]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
