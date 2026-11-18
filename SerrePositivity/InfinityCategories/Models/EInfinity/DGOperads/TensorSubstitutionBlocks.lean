module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSubstitutionAssociativity
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSubstitutionMiddle
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSubstitutionSquares

/-!
模型。文献の定義との比較は後で
# 二つの入力ブロックへのテンソル代入

概要：Berger–Moerdijk §1 の入力ブロック分解で、末尾の代入と後半の再結合を比較する。
方針：末尾因子の射の自然性、二段の代入の結合則、中間因子の自然性を順に使う。
規約：後半の再結合は同型で与え、前半の順序は保つ。
使われ方：反復合成の二ブロックへの分解の帰納段階を処理する。
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

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep

/-- 概要：末尾の代入因子の射は最初の係数射の前へ移せる（Berger–Moerdijk §1）。
方針：三入力の自然性に、係数と残りの入力の恒等射を指定する。
規約：末尾因子の始域と終域は異なってよい。
使われ方：後半の最後の因子の分離を代入の前後へ移す。 -/
lemma tensorSubstitutionStep_last {R V L L' S O : Complex A}
    (f : R ⊗ L' ⟶ S) (g : S ⊗ V ⟶ O) (a : L ⟶ L') :
    (R ◁ (V ◁ a)) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep f g =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep ((R ◁ a) ≫ f) g := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep_naturality ((R ◁ a) ≫ f) g f g
    (𝟙 R) (𝟙 V) a (𝟙 S) (𝟙 O)
    (by simp only [id_tensorHom, Category.comp_id])
    (by simp only [tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id])
  simpa only [id_tensorHom, Category.comp_id] using h

/-- 概要：後半を最後の因子と残りへ分けた二段の代入は、後半全体の代入に一致する（Berger–Moerdijk §1）。
方針：再結合の逆射を末尾因子の自然性で相殺し、代入の結合則と中間因子の自然性を使う。
規約：a は残りの入力の分離、b は後半の最後の因子の分離。
使われ方：有限入力族の二ブロックへの分離に伴う代入順序の比較となる。 -/
lemma tensorSubstitutionStep_blocks {R Q V U L T R₁ R₂ O : Complex A}
    (a : Q ⟶ V ⊗ U) (b : T ≅ U ⊗ L)
    (f : R ⊗ L ⟶ R₁) (g : R₁ ⊗ U ⟶ R₂) (h : R₂ ⊗ V ⟶ O) :
    (R ◁ ((a ▷ L) ≫ (α_ V U L).hom ≫ (V ◁ b.inv))) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep ((R ◁ b.hom) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep f g) h =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep f ((R₁ ◁ a) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep g h) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep_last (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep f g) h b.hom]
  simp only [whiskerLeft_comp, Category.assoc]
  conv_lhs =>
    arg 2
    arg 2
    simp only [← whiskerLeft_comp_assoc, ← whiskerLeft_comp, Iso.inv_hom_id,
      whiskerLeft_id, Category.id_comp]
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep_assoc f g h]
  simpa only [tensorHom_id] using
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep_middle f (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep g h) a

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
