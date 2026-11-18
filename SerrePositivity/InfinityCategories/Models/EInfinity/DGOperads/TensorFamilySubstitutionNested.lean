module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSubstitutionNested

/-!
模型。文献の定義との比較は後で
# 有限族の入れ子のテンソル代入

概要：Berger–Moerdijk §1 の入れ子の部分合成を有限族の末尾からの代入と両立させる。
方針：最後の因子を分離し、二つの結合則を一段の代入の比較へ適用する。
規約：外側係数 R と内側係数 S は交換しない。
使われ方：反復合成と部分合成の両立を入力族の長さで帰納する。
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

/-- 概要：入れ子の代入の比較は最後の因子の分離と両立する（Berger–Moerdijk §1）。
方針：外側合成を分離の前後へ移し、一段の代入の入れ子の比較を使う。
規約：残りの演算のテンソルの順序は保つ。
使われ方：オペラッドの反復合成の結合則の帰納段階を構成する。 -/
lemma tensorFamilySubstitutionStep_nested (n : ℕ) (V : Fin (n + 1) → Complex A)
    {R S T S₁ S₂ T₁ O : Complex A}
    (f : R ⊗ S ⟶ T) (g : S ⊗ V (Fin.last n) ⟶ S₁)
    (h : T ⊗ V (Fin.last n) ⟶ T₁) (p : R ⊗ S₁ ⟶ T₁)
    (v : T₁ ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc) ⟶ O)
    (w : S₁ ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc) ⟶ S₂) (q : R ⊗ S₂ ⟶ O)
    (hf : (f ▷ V (Fin.last n)) ≫ h =
      (α_ R S (V (Fin.last n))).hom ≫ (R ◁ g) ≫ p)
    (hv : (p ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc)) ≫ v =
      (α_ R S₁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc))).hom ≫ (R ◁ w) ≫ q) :
    (f ▷ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 1) V) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep n V h v =
      (α_ R S (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 1) V)).hom ≫
        (R ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep n V g w) ≫ q := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySubstitutionStep
  rw [← whisker_exchange_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep_nested f g h p v w q hf hv]
  rw [associator_naturality_right_assoc]
  simp only [whiskerLeft_comp, Category.assoc]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
