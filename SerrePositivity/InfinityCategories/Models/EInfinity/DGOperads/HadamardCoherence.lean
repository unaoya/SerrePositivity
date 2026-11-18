module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSeparationBraiding

/-!
模型。文献の定義との比較は後で
# Arity ごとのテンソル積の整合性

概要：Berger–Moerdijk §1 のオペラッドのテンソル積に必要な六因子の分離を記述する。
方針：tensorμ の自然性・結合則・対称性から共通の比較射を作る。
規約：任意の対称モノイダル圏で、左右二列の対象は独立でよい。
使われ方：Hadamard 積の入れ子・独立な部分合成の結合則を証明する。
-/

@[expose] public section

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- 概要：左括弧の三対を二つの三因子へ分離する（Berger–Moerdijk §1）。
方針：tensorμ を二回適用する。
規約：分離後も左括弧を保つ。
使われ方：二回の部分合成を二列に分ける共通の前置射となる。 -/
def separate (X X' Y Y' Z Z' : C) :
    ((X ⊗ X') ⊗ (Y ⊗ Y')) ⊗ (Z ⊗ Z') ⟶ ((X ⊗ Y) ⊗ Z) ⊗ ((X' ⊗ Y') ⊗ Z') :=
  (tensorμ X X' Y Y' ▷ (Z ⊗ Z')) ≫ tensorμ (X ⊗ Y) (X' ⊗ Y') Z Z'

/-- 概要：三対の分離と結合子は可換である（Berger–Moerdijk §1）。
方針：標準の tensor_associativity を再利用する。
規約：右辺の二列は右括弧になる。
使われ方：Hadamard 積の入れ子の結合則の前置射を揃える。 -/
@[reassoc]
lemma separate_assoc (X X' Y Y' Z Z' : C) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.separate X X' Y Y' Z Z' ≫ ((α_ X Y Z).hom ⊗ₘ (α_ X' Y' Z').hom) =
      (α_ (X ⊗ X') (Y ⊗ Y') (Z ⊗ Z')).hom ≫
      ((X ⊗ X') ◁ tensorμ Y Y' Z Z') ≫ tensorμ X X' (Y ⊗ Z) (Y' ⊗ Z') :=
  by simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.separate, Category.assoc] using tensor_associativity X X' Y Y' Z Z'

/-- 概要：後二対の交換は分離後の各列の交換になる（Berger–Moerdijk §1）。
方針：結合子の整合性と tensorμ_braiding の間で自然性を使う。
規約：三因子全体を左括弧に戻して比較する。
使われ方：Hadamard 積の独立な二つの代入の結合則に用いる。 -/
@[reassoc]
lemma separate_swap (X X' Y Y' Z Z' : C) :
    (α_ (X ⊗ X') (Y ⊗ Y') (Z ⊗ Z')).hom ≫
      ((X ⊗ X') ◁ (β_ (Y ⊗ Y') (Z ⊗ Z')).hom) ≫
      (α_ (X ⊗ X') (Z ⊗ Z') (Y ⊗ Y')).inv ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.separate X X' Z Z' Y Y' =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.separate X X' Y Y' Z Z' ≫
      (((α_ X Y Z).hom ≫ (X ◁ (β_ Y Z).hom) ≫ (α_ X Z Y).inv) ⊗ₘ
        ((α_ X' Y' Z').hom ≫ (X' ◁ (β_ Y' Z').hom) ≫ (α_ X' Z' Y').inv)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.separate, Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorμ_associativity_inv, ← whiskerLeft_comp_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorμ_braiding]
  simp only [whiskerLeft_comp, Category.assoc]
  rw [tensorμ_natural_right_assoc]
  rw [← tensor_associativity_assoc]
  simp only [← tensorHom_comp_tensorHom]


/-- 概要：二列の二項演算をテンソル対の演算にする（Berger–Moerdijk §1）。
方針：四因子を分離してから各列に演算を適用する。
規約：四因子の交換は圏の対称性を使う。
使われ方：Hadamard 積の部分合成の定義となる。 -/
def pair {X X' Y Y' U U' : C} (f : X ⊗ Y ⟶ U) (g : X' ⊗ Y' ⟶ U') :
    (X ⊗ X') ⊗ (Y ⊗ Y') ⟶ U ⊗ U' :=
  tensorμ X X' Y Y' ≫ (f ⊗ₘ g)

/-- 概要：対の演算の左側での反復合成を分離する（Berger–Moerdijk §1）。
方針：tensorμ の左自然性で中間演算を後ろへ移す。
規約：三因子の括弧は左括弧。
使われ方：二種類の結合則の左辺を各列の合成へ帰着する。 -/
@[reassoc]
lemma pair_left {X X' Y Y' Z Z' U U' V V' : C}
    (f : X ⊗ Y ⟶ U) (f' : X' ⊗ Y' ⟶ U')
    (g : U ⊗ Z ⟶ V) (g' : U' ⊗ Z' ⟶ V') :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.pair f f' ▷ (Z ⊗ Z')) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.pair g g' =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.separate X X' Y Y' Z Z' ≫ ((f ▷ Z ≫ g) ⊗ₘ (f' ▷ Z' ≫ g')) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.pair, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.separate, comp_whiskerRight, Category.assoc]
  rw [tensorμ_natural_left_assoc, tensorHom_comp_tensorHom]

/-- 概要：対の演算の右側での反復合成を分離する（Berger–Moerdijk §1）。
方針：tensorμ の右自然性と結合則を適用する。
規約：始域を左括弧に揃えるため結合子を前置する。
使われ方：入れ子の結合則の右辺を各列の合成へ帰着する。 -/
@[reassoc]
lemma pair_right {X X' Y Y' Z Z' U U' V V' : C}
    (f : Y ⊗ Z ⟶ U) (f' : Y' ⊗ Z' ⟶ U')
    (g : X ⊗ U ⟶ V) (g' : X' ⊗ U' ⟶ V') :
    (α_ (X ⊗ X') (Y ⊗ Y') (Z ⊗ Z')).hom ≫
      ((X ⊗ X') ◁ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.pair f f') ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.pair g g' =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.separate X X' Y Y' Z Z' ≫
      (((α_ X Y Z).hom ≫ (X ◁ f) ≫ g) ⊗ₘ
        ((α_ X' Y' Z').hom ≫ (X' ◁ f') ≫ g')) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.pair, whiskerLeft_comp, Category.assoc]
  rw [tensorμ_natural_right_assoc, ← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.separate_assoc_assoc]
  simp only [← tensorHom_comp_tensorHom]


/-- 概要：対の演算への後合成は二列へ分離する（Berger–Moerdijk §1）。
方針：テンソルの合成保存則を使う。
規約：出力の射は二列で独立でよい。
使われ方：arity の移送を部分合成へ吸収する。 -/
@[reassoc]
lemma pair_post {X X' Y Y' U U' V V' : C}
    (f : X ⊗ Y ⟶ U) (f' : X' ⊗ Y' ⟶ U') (g : U ⟶ V) (g' : U' ⟶ V') :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.pair f f' ≫ (g ⊗ₘ g') = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.pair (f ≫ g) (f' ≫ g') := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.pair, Category.assoc, tensorHom_comp_tensorHom]

/-- 概要：移送を挟んだ左側の反復合成を分離する（Berger–Moerdijk §1）。
方針：後合成を吸収してから左側の反復合成の分離を適用する。
規約：中間の射をテンソル因子ごとに指定する。
使われ方：独立な二代入の arity の移送を扱う。 -/
@[reassoc]
lemma pair_left_post {X X' Y Y' Z Z' U U' T T' V V' : C}
    (f : X ⊗ Y ⟶ U) (f' : X' ⊗ Y' ⟶ U') (t : U ⟶ T) (t' : U' ⟶ T')
    (g : T ⊗ Z ⟶ V) (g' : T' ⊗ Z' ⟶ V') :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.pair f f' ▷ (Z ⊗ Z')) ≫ ((t ⊗ₘ t') ▷ (Z ⊗ Z')) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.pair g g' =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.separate X X' Y Y' Z Z' ≫
      ((f ▷ Z ≫ t ▷ Z ≫ g) ⊗ₘ (f' ▷ Z' ≫ t' ▷ Z' ≫ g')) := by
  rw [← comp_whiskerRight_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.pair_post, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard.pair_left]
  simp only [comp_whiskerRight, Category.assoc]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.Hadamard
