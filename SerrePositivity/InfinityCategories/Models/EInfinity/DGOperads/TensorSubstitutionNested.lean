module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSubstitutionAssociativity

/-!
模型。文献の定義との比較は後で
# 入れ子のテンソル代入

概要：Berger–Moerdijk §1 の入れ子の部分合成を、末尾から行う反復代入へ移す。
方針：外側合成と末尾の代入の結合則、残りの代入の結合則を構造射の自然性で接続する。
規約：外側の係数は固定し、残りの演算族 V の最後に L を置く。
使われ方：全入力への合成と部分合成の両立の帰納段階を処理する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]

/-- 概要：外側の係数を保った四因子の交換の括弧付けを比較する（Berger–Moerdijk §1）。
方針：結合子の自然性で一つの交換射を移し、pentagon の整合性を適用する。
規約：V,L だけを交換し、R,S は交換しない。
使われ方：入れ子の反復代入の構造射を比較する。 -/
@[reassoc]
lemma substitutionNested_coherence (R S V L : C) :
    ((R ⊗ S) ◁ (β_ V L).hom) ≫ (α_ (R ⊗ S) L V).inv ≫
      ((α_ R S L).hom ▷ V) ≫ (α_ R (S ⊗ L) V).hom =
    (α_ R S (V ⊗ L)).hom ≫ (R ◁ (S ◁ (β_ V L).hom)) ≫
      (R ◁ (α_ S L V).inv) := by
  rw [← associator_naturality_right_assoc]
  monoidal

/-- 概要：末尾の代入と残りの代入の結合則を、入れ子の代入全体へ拡張する（Berger–Moerdijk §1）。
方針：外側合成を交換と結合子へ通し、二つの結合則を適用して構造射を整理する。
規約：f は外側合成、g は内側の末尾の代入、w は残りの代入。
使われ方：オペラッドの nested_assoc から反復合成の結合則を帰納的に示す。 -/
lemma tensorSubstitutionStep_nested {A : Type u} [CommRing A]
    {R S V L T S₁ S₂ T₁ O : _root_.SerrePositivity.DifferentialGraded.Complex A}
    (f : R ⊗ S ⟶ T) (g : S ⊗ L ⟶ S₁) (h : T ⊗ L ⟶ T₁)
    (p : R ⊗ S₁ ⟶ T₁) (v : T₁ ⊗ V ⟶ O) (w : S₁ ⊗ V ⟶ S₂) (q : R ⊗ S₂ ⟶ O)
    (hf : (f ▷ L) ≫ h = (α_ R S L).hom ≫ (R ◁ g) ≫ p)
    (hv : (p ▷ V) ≫ v = (α_ R S₁ V).hom ≫ (R ◁ w) ≫ q) :
    (f ▷ (V ⊗ L)) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep h v =
      (α_ R S (V ⊗ L)).hom ≫ (R ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep g w) ≫ q := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep
  rw [← whisker_exchange_assoc, associator_inv_naturality_left_assoc]
  rw [← comp_whiskerRight_assoc, hf]
  simp only [comp_whiskerRight, Category.assoc]
  rw [hv, associator_naturality_middle_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.substitutionNested_coherence_assoc]
  simp only [whiskerLeft_comp, Category.assoc]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
