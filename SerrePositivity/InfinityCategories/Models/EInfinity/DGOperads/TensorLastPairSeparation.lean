module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorLastPairExtraction
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSeparationBraiding

/-!
模型。文献の定義との比較は後で
# 最後の係数の取り出しと係数・入力の分離

概要：Berger–Moerdijk §1 の反復合成で、最後の係数を取り出す順序と全体を分離する順序を比較する。
方針：係数と入力の交換を展開し、交換の六角形の式と結合子の整合性を用いる。
規約：入力の列の順序を保存する。
使われ方：反復合成のテンソル射を最後の演算に沿って分解する。
-/

@[expose] public section

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.BraidedCategory

variable {C₀ : Type u} [Category.{v} C₀] [MonoidalCategory C₀] [SymmetricCategory C₀]

/-- 概要：最後の係数の取り出しは係数列・入力列への分離と両立する（Berger–Moerdijk §1）。
方針：前半の二因子と最後の係数の交換を六角形の式で二段の交換へ分ける。
規約：出力の係数の順序は R,L,V、入力の順序は W,Z,T。
使われ方：部分合成の再帰と入力の連結の再帰を一つのテンソル射で比較する。 -/
@[reassoc]
lemma tensorLastPairSeparation_coherence (R V W L Z T : C₀) :
    (R ◁ (tensorμ V W L Z ▷ T)) ≫
      (R ◁ (α_ (V ⊗ L) (W ⊗ Z) T).hom) ≫
      (α_ R (V ⊗ L) ((W ⊗ Z) ⊗ T)).inv ≫
      (((R ◁ (β_ V L).hom) ≫ (α_ R L V).inv) ⊗ₘ (α_ W Z T).hom) =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorLastPairExtraction R (V ⊗ W) L Z T ≫
      ((R ⊗ L) ◁ (α_ V W (Z ⊗ T)).hom) ≫
      (α_ (R ⊗ L) V (W ⊗ (Z ⊗ T))).inv := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorLastPairExtraction
  rw [braiding_tensor_left_hom]
  simp only [tensorμ, tensorHom_def, comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  monoidal

/-- 概要：最後の係数を合成してから前半を合成する計算を分離射へ通せる（Berger–Moerdijk §1）。
方針：構造射の比較に係数と入力の射を後合成し、結合子の自然性を使う。
規約：前半の入力射 a と最後と末尾の入力射 b は独立。
使われ方：反復合成の再帰を、最後の係数の部分合成と残りの全合成へ分解する。 -/
lemma tensorLastPairSeparation {R V W L Z T R' O W' T' U : C₀}
    (f : R ⊗ L ⟶ R') (g : R' ⊗ V ⟶ O) (a : W ⟶ W')
    (b : Z ⊗ T ⟶ T') (c : W' ⊗ T' ⟶ U) :
    (R ◁ (tensorμ V W L Z ▷ T)) ≫
      (R ◁ (α_ (V ⊗ L) (W ⊗ Z) T).hom) ≫
      (α_ R (V ⊗ L) ((W ⊗ Z) ⊗ T)).inv ≫
      (((R ◁ (β_ V L).hom) ≫ (α_ R L V).inv ≫ (f ▷ V) ≫ g) ⊗ₘ
        ((α_ W Z T).hom ≫ (a ⊗ₘ b) ≫ c)) =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorLastPairExtraction R (V ⊗ W) L Z T ≫
      (f ⊗ₘ ((α_ V W (Z ⊗ T)).hom ≫ (V ◁ (a ⊗ₘ b)))) ≫
      (α_ R' V (W' ⊗ T')).inv ≫ (g ⊗ₘ c) := by
  have h := congrArg (fun z => z ≫ ((f ▷ V) ⊗ₘ (a ⊗ₘ b)) ≫ (g ⊗ₘ c))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorLastPairSeparation_coherence R V W L Z T)
  simp only [Category.assoc, tensorHom_comp_tensorHom] at h
  calc
    _ = _ := h
    _ = _ := by
      rw [← tensorHom_comp_tensorHom (f ▷ V) (a ⊗ₘ b) g c]
      have hn := associator_inv_naturality f (𝟙 V) (a ⊗ₘ b)
      simp only [tensorHom_id, id_tensorHom] at hn
      rw [← reassoc_of% hn, whiskerLeft_comp_tensorHom_assoc]

/-- 概要：前半の任意の分離射を含めて最後の係数を先に合成できる（Berger–Moerdijk §1）。
方針：分離射を前合成し、係数の取り出しの自然性で後へ移す。
規約：前半の演算族は任意の対象 S と射 v で表せる。
使われ方：有限テンソル族の分離同型を使う反復合成の再帰に適用する。 -/
lemma tensorLastPairSeparation_maps {R S V W L Z T R' O W' T' U : C₀}
    (v : S ⟶ V ⊗ W) (f : R ⊗ L ⟶ R') (g : R' ⊗ V ⟶ O) (a : W ⟶ W')
    (b : Z ⊗ T ⟶ T') (c : W' ⊗ T' ⟶ U) :
    (R ◁ ((v ▷ (L ⊗ Z)) ▷ T)) ≫
      (R ◁ (tensorμ V W L Z ▷ T)) ≫
      (R ◁ (α_ (V ⊗ L) (W ⊗ Z) T).hom) ≫
      (α_ R (V ⊗ L) ((W ⊗ Z) ⊗ T)).inv ≫
      (((R ◁ (β_ V L).hom) ≫ (α_ R L V).inv ≫ (f ▷ V) ≫ g) ⊗ₘ
        ((α_ W Z T).hom ≫ (a ⊗ₘ b) ≫ c)) =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorLastPairExtraction R S L Z T ≫
      (f ⊗ₘ ((v ▷ (Z ⊗ T)) ≫ (α_ V W (Z ⊗ T)).hom ≫ (V ◁ (a ⊗ₘ b)))) ≫
      (α_ R' V (W' ⊗ T')).inv ≫ (g ⊗ₘ c) := by
  have h := congrArg (fun z => (R ◁ ((v ▷ (L ⊗ Z)) ▷ T)) ≫ z)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorLastPairSeparation f g a b c)
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorLastPairExtraction_naturality_assoc, whiskerLeft_comp_tensorHom_assoc] at h
  exact h

/-- 概要：最後の演算の係数と入力を処理した後に前半の反復合成を行える（Berger–Moerdijk §1）。
方針：最後の入力の射を前半の分離より前へ移し、残りを同じ形のテンソル射へまとめる。
規約：f は最後の係数の合成、b は最後の入力と未処理の末尾の連結。
使われ方：末尾入力を残した反復合成のテンソル射の再帰を記述する。 -/
lemma tensorLastPairIteration {R S V W L Z T R' O W' T' U : C₀}
    (v : S ⟶ V ⊗ W) (f : R ⊗ L ⟶ R') (g : R' ⊗ V ⟶ O) (a : W ⟶ W')
    (b : Z ⊗ T ⟶ T') (c : W' ⊗ T' ⟶ U) :
    (R ◁ ((v ▷ (L ⊗ Z)) ▷ T)) ≫
      (R ◁ (tensorμ V W L Z ▷ T)) ≫
      (R ◁ (α_ (V ⊗ L) (W ⊗ Z) T).hom) ≫
      (α_ R (V ⊗ L) ((W ⊗ Z) ⊗ T)).inv ≫
      (((R ◁ (β_ V L).hom) ≫ (α_ R L V).inv ≫ (f ▷ V) ≫ g) ⊗ₘ
        ((α_ W Z T).hom ≫ (a ⊗ₘ b) ≫ c)) =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorLastPairExtraction R S L Z T ≫ (f ⊗ₘ (S ◁ b)) ≫
      (R' ◁ (v ▷ T')) ≫ (R' ◁ (α_ V W T').hom) ≫
      (α_ R' V (W ⊗ T')).inv ≫ (g ⊗ₘ ((a ▷ T') ≫ c)) := by
  have hi : (v ▷ (Z ⊗ T)) ≫ (α_ V W (Z ⊗ T)).hom ≫ (V ◁ (a ⊗ₘ b)) =
      (S ◁ b) ≫ (v ▷ T') ≫ (α_ V W T').hom ≫ (V ◁ (a ▷ T')) := by
    rw [tensorHom_def']
    simp only [whiskerLeft_comp]
    rw [← associator_naturality_right_assoc, ← whisker_exchange_assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorLastPairSeparation_maps, hi]
  simp only [← tensorHom_comp_whiskerLeft, whiskerLeft_comp, Category.assoc]
  rw [associator_inv_naturality_right_assoc, whiskerLeft_comp_tensorHom]
  rw [tensorHom_comp_whiskerLeft]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
