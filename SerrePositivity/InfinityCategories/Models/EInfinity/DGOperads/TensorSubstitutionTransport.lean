module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSubstitutionMiddle

/-!
模型。文献の定義との比較は後で
# テンソル代入の係数と中間対象の移送

概要：Berger–Moerdijk §1 の部分合成の arity の移送を、テンソル代入の前後へまとめる。
方針：係数についての自然性と whisker の合成則を使う。
規約：残りの入力 V と最後の入力 L の順序を保つ。
使われ方：反復合成の二段を、任意の二位置への合成射の arity の表記へ移す。
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

/-- 概要：係数射はテンソル代入の前へ移せる（Berger–Moerdijk §1）。
方針：braiding と結合子の自然性で係数射を最初の部分合成の前へ移す。
規約：係数の始域と終域は異なってよい。
使われ方：外側 arity の移送を二入力への代入全体の前へまとめる。 -/
lemma tensorSubstitutionStep_first_pre {R₀ R V L R' O : Complex A}
    (a : R₀ ⟶ R) (f : R ⊗ L ⟶ R') (g : R' ⊗ V ⟶ O) :
    (a ▷ (V ⊗ L)) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep f g =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep ((a ▷ L) ≫ f) g := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep, comp_whiskerRight, Category.assoc]
  rw [← whisker_exchange_assoc a (β_ V L).hom,
    associator_inv_naturality_left_assoc a L V]

/-- 概要：最初の部分合成の後の射は次の係数の移送へまとめられる（Berger–Moerdijk §1）。
方針：右 whisker が合成を保つことを使う。
規約：中間対象の射は任意。
使われ方：二つの部分合成の間の arity の移送を合成する。 -/
lemma tensorSubstitutionStep_first_post {R V L R' R'' O : Complex A}
    (f : R ⊗ L ⟶ R') (t : R' ⟶ R'') (g : R'' ⊗ V ⟶ O) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep (f ≫ t) g = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep f ((t ▷ V) ≫ g) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep, comp_whiskerRight, Category.assoc]

/-- 概要：係数の移送と二つの中間の移送をテンソル代入の前と中間へまとめる（Berger–Moerdijk §1）。
方針：係数射の自然性を使い、中間の二射を右 whisker の合成則でまとめる。
規約：二つの中間射の始域と終域はそれぞれ独立に指定する。
使われ方：反復合成の二段の arity の表記を二位置への合成の表記とそろえる。 -/
lemma tensorSubstitutionStep_transport {R₀ R V L S S' S'' O : Complex A}
    (a : R₀ ⟶ R) (f : R ⊗ L ⟶ S) (t : S ⟶ S') (u : S' ⟶ S'')
    (g : S'' ⊗ V ⟶ O) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep ((a ▷ L) ≫ f ≫ t) ((u ▷ V) ≫ g) =
      (a ▷ (V ⊗ L)) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep f (((t ≫ u) ▷ V) ≫ g) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep_first_pre, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorSubstitutionStep_first_post]
  rw [← comp_whiskerRight_assoc]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
