module

public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
模型。文献の定義との比較は後で
# 末尾の演算対から係数を取り出す構造射

概要：Berger–Moerdijk §1 の反復合成で最後の演算の係数を外側の係数の直後へ移す。
方針：最後の係数だけを前半の演算族と交換し、その入力は末尾入力の前に残す。
規約：対称性の交換に含まれる符号を変更しない。
使われ方：係数の反復合成の再帰を、係数と入力を含む全体の射の再帰へ移す。
-/

@[expose] public section

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.BraidedCategory

variable {C₀ : Type u} [Category.{v} C₀] [MonoidalCategory C₀] [BraidedCategory C₀]

/-- 概要：末尾の演算対から係数だけを外側の係数の直後へ取り出す射（Berger–Moerdijk §1）。
方針：最後の入力 Z と末尾 T をまとめ、係数 L を前半 S の前へ交換する。
規約：最終の順序は R,L,S,Z,T。
使われ方：最後の指定入力への部分合成をテンソル全体で先に行う。 -/
def tensorLastPairExtraction (R S L Z T : C₀) :
    R ⊗ ((S ⊗ (L ⊗ Z)) ⊗ T) ⟶ (R ⊗ L) ⊗ (S ⊗ (Z ⊗ T)) :=
  (R ◁ (α_ S (L ⊗ Z) T).hom) ≫
    (R ◁ (S ◁ (α_ L Z T).hom)) ≫
    (R ◁ (α_ S L (Z ⊗ T)).inv) ≫
    (R ◁ ((β_ S L).hom ▷ (Z ⊗ T))) ≫
    (R ◁ (α_ L S (Z ⊗ T)).hom) ≫
    (α_ R L (S ⊗ (Z ⊗ T))).inv

/-- 概要：末尾係数の取り出しは前半の演算族の射と両立する（Berger–Moerdijk §1）。
方針：前半の射を結合子の自然性で交換の直前へ移し、交換の自然性を使う。
規約：最後の係数と二つの入力ブロックは固定する。
使われ方：前半の係数と入力の分離を、最後の係数の取り出しに通す。 -/
@[reassoc]
lemma tensorLastPairExtraction_naturality (R L Z T : C₀) {S S' : C₀} (a : S ⟶ S') :
    (R ◁ ((a ▷ (L ⊗ Z)) ▷ T)) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorLastPairExtraction R S' L Z T =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorLastPairExtraction R S L Z T ≫ ((R ⊗ L) ◁ (a ▷ (Z ⊗ T))) := by
  calc
    _ = (R ◁ (α_ S (L ⊗ Z) T).hom) ≫
        (R ◁ (S ◁ (α_ L Z T).hom)) ≫
        (R ◁ (α_ S L (Z ⊗ T)).inv) ≫
        (R ◁ (((a ▷ L) ≫ (β_ S' L).hom) ▷ (Z ⊗ T))) ≫
        (R ◁ (α_ L S' (Z ⊗ T)).hom) ≫
        (α_ R L (S' ⊗ (Z ⊗ T))).inv := by
      unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorLastPairExtraction
      simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
      monoidal
    _ = _ := by
      rw [braiding_naturality_left]
      unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorLastPairExtraction
      simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
      monoidal

/-- 概要：前半の評価射を最後の係数の取り出しの前へ移せる（Berger–Moerdijk §1）。
方針：係数の取り出しの自然性と独立なテンソル射の交換則を使う。
規約：最後の入力と末尾の射 b は前半の射 a と独立に適用する。
使われ方：反復合成の評価の帰納仮定の後で、前半の作用を部分合成の入力へ移す。 -/
@[reassoc]
lemma tensorLastPairExtraction_map_prefix {R D V L Z T R' T' W : C₀}
    (a : D ⟶ V) (f : R ⊗ L ⟶ R') (b : Z ⊗ T ⟶ T') (c : V ⊗ T' ⟶ W) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorLastPairExtraction R D L Z T ≫ (f ⊗ₘ (D ◁ b)) ≫
      (R' ◁ ((a ⊗ₘ 𝟙 T') ≫ c)) =
    (R ◁ ((a ▷ (L ⊗ Z)) ▷ T)) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorLastPairExtraction R V L Z T ≫
      (f ⊗ₘ ((V ◁ b) ≫ c)) := by
  rw [tensorHom_id, tensorHom_comp_whiskerLeft, whisker_exchange_assoc,
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorLastPairExtraction_naturality_assoc, whiskerLeft_comp_tensorHom]

/-- 概要：取り出した係数を同じ前半の後へ戻して作用させると二つの交換は相殺する（Berger–Moerdijk §1）。
方針：結合子とその逆射を除き、対称性による反対向きの交換を相殺する。
規約：入力 Z と末尾 T の順序を変えない。
使われ方：最後の係数の合成を代数の作用へ変えた後、元の入力順序に戻す。 -/
lemma tensorLastPairExtraction_reinsert {C₁ : Type u} [Category.{v} C₁]
    [MonoidalCategory C₁] [SymmetricCategory C₁] (R S L Z T X : C₁)
    (θ : L ⊗ Z ⟶ X) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorLastPairExtraction R S L Z T ≫ (α_ R L (S ⊗ (Z ⊗ T))).hom ≫
      (R ◁ ((α_ L S (Z ⊗ T)).inv ≫
        ((β_ L S).hom ▷ (Z ⊗ T)) ≫ (α_ S L (Z ⊗ T)).hom ≫
        (S ◁ (α_ L Z T).inv) ≫ (S ◁ (θ ▷ T)))) =
      (R ◁ (α_ S (L ⊗ Z) T).hom) ≫ (R ◁ (S ◁ (θ ▷ T))) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorLastPairExtraction
  simp only [whiskerLeft_comp, Category.assoc, Iso.inv_hom_id_assoc,
    whiskerLeft_hom_inv_assoc]
  rw [SymmetricCategory.braiding_swap_eq_inv_braiding L S]
  have hb : (R ◁ ((β_ L S).inv ▷ (Z ⊗ T))) ≫
      (R ◁ ((β_ L S).hom ▷ (Z ⊗ T))) = 𝟙 _ := by
    rw [← whiskerLeft_comp, ← comp_whiskerRight, Iso.inv_hom_id,
      id_whiskerRight, whiskerLeft_id]
  rw [reassoc_of% hb]
  monoidal

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
