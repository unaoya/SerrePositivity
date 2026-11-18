module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionAssembly
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSubstitutionAssociativity

/-!
模型。文献の定義との比較は後で
# 二段の convolution 図式

概要：Berger–Fresse §3.1 の入れ子の convolution の組み立てを一つの図式へまとめる。
方針：係数の分配と余演算・作用をそれぞれ合成し、交換と結合子の自然性を使う。
規約：余演算の順序は外側を先、内側を後とする。
使われ方：Hopf 対角・代数・余代数の部分合成則を convolution に移す。
-/

@[expose] public section

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

variable {K : Type u} [Category.{v} K] [MonoidalCategory K] [SymmetricCategory K]

private lemma composition_core {C D E F V H W Z T Y B : K}
    (θ : D ⊗ H ⟶ W) (ψ : F ⊗ W ⟶ Z) (e : V ⊗ Z ⟶ T)
    (a : E ⊗ T ⟶ Y) (b : C ⊗ Y ⟶ B) :
    ((α_ (C ⊗ D) (E ⊗ F) V).hom ▷ H) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly (𝟙 (C ⊗ D)) θ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly (𝟙 (E ⊗ F)) ψ e a) b =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly (tensorμ C D E F)
      (((β_ D F).hom ▷ H) ≫ (α_ F D H).hom ≫ (F ◁ θ) ≫ ψ)
      e ((α_ C E T).hom ≫ (C ◁ a) ≫ b) := by
  let N : (((C ⊗ D) ⊗ (E ⊗ F)) ⊗ V) ⊗ H ⟶ B :=
    𝟙 _ ⊗≫ ((C ◁ (β_ D E).hom) ▷ F ▷ V ▷ H) ⊗≫
      ((C ⊗ E) ◁ (((α_ D F V).hom ≫ (β_ D (F ⊗ V)).hom ≫
        ((β_ F V).hom ▷ D) ≫ (α_ V F D).hom) ▷ H)) ⊗≫
      ((C ⊗ E) ◁ (V ◁ (F ◁ θ))) ⊗≫ ((C ⊗ E) ◁ (V ◁ ψ)) ⊗≫
      ((C ⊗ E) ◁ e) ⊗≫ (C ◁ a) ⊗≫ b
  let N₀ : (((C ⊗ D) ⊗ (E ⊗ F)) ⊗ V) ⊗ H ⟶ B :=
    𝟙 _ ⊗≫ ((C ◁ (β_ D E).hom) ▷ F ▷ V ▷ H) ⊗≫
      ((C ⊗ E) ◁ ((β_ D (F ⊗ V)).hom ▷ H)) ⊗≫
      ((C ⊗ E) ◁ ((β_ F V).hom ⊗ₘ θ)) ⊗≫
      ((C ⊗ E) ◁ (V ◁ ψ)) ⊗≫ ((C ⊗ E) ◁ e) ⊗≫ (C ◁ a) ⊗≫ b
  calc
    _ = N₀ := by
      dsimp only [N₀]
      rw [tensorHom_def' (β_ F V).hom θ]
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly, tensorμ, id_whiskerRight,
        Category.id_comp, comp_whiskerRight, whiskerLeft_comp, Category.assoc,
        BraidedCategory.braiding_tensor_right_hom]
      monoidal
    _ = N := by
      dsimp only [N₀, N]
      rw [tensorHom_def (β_ F V).hom θ]
      simp only [comp_whiskerRight, whiskerLeft_comp]
      monoidal
    _ = _ := by
      dsimp only [N]
      rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.substitutionBraiding_three]
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly, tensorμ, comp_whiskerRight, whiskerLeft_comp,
        Category.assoc, BraidedCategory.braiding_tensor_left_hom]
      monoidal

/-- 概要：二段の組み立ては係数の対角と余演算・作用を合成した組み立て（BF §3.1）。
方針：係数の自然性で恒等分配に戻し、三因子の交換の整合性を使う。
規約：内側の係数 Q とその入力 V を外側の入力として扱う。
使われ方：convolution の部分合成公理の評価後の等式を閉じる。 -/
lemma convolutionAssembly_composition {O C D Q E F V H W Z T Y B : K}
    (d : O ⟶ C ⊗ D) (q : Q ⟶ E ⊗ F)
    (θ : D ⊗ H ⟶ W) (ψ : F ⊗ W ⟶ Z) (e : V ⊗ Z ⟶ T)
    (a : E ⊗ T ⟶ Y) (b : C ⊗ Y ⟶ B) :
    ((α_ O Q V).hom ▷ H) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly d θ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly q ψ e a) b =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly ((d ⊗ₘ q) ≫ tensorμ C D E F)
      (((β_ D F).hom ▷ H) ≫ (α_ F D H).hom ≫ (F ◁ θ) ≫ ψ)
      e ((α_ C E T).hom ≫ (C ◁ a) ≫ b) := by
  have hn := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly_naturality d θ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly q ψ e a) b
    (𝟙 (C ⊗ D)) θ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly (𝟙 (E ⊗ F)) ψ e a) b
    d (𝟙 C) (𝟙 D) (q ▷ V) (𝟙 H) (𝟙 W) (𝟙 Y) (𝟙 B)
    (by simp only [Category.comp_id, tensorHom_id, id_whiskerRight])
    (by simp only [tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id])
    (by simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly, tensorHom_id, id_whiskerRight,
      Category.id_comp, Category.comp_id])
    (by simp only [tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id])
  simp only [tensorHom_id, Category.comp_id] at hn
  have hcoeff : ((α_ O Q V).hom ▷ H) ≫ ((d ⊗ₘ (q ▷ V)) ▷ H) =
      ((d ⊗ₘ q) ▷ V ▷ H) ≫ ((α_ (C ⊗ D) (E ⊗ F) V).hom ▷ H) := by
    simp only [← comp_whiskerRight]
    congr 1
    simpa only [tensorHom_id] using (associator_naturality d q (𝟙 V)).symm
  rw [← hn, ← Category.assoc, hcoeff, Category.assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.composition_core]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly, comp_whiskerRight, Category.assoc]

/-- 概要：入力への射の適用を組み立ての評価へ移す（BF §3.1）。
方針：後合成の自然性で中間と最終の出力射を恒等射にする。
規約：係数の分配と余演算を固定する。
使われ方：convolution の内側演算の代入を評価してから二段の図式へ移す。 -/
lemma convolutionAssembly_input {O C D V V' H W T B : K}
    (d : O ⟶ C ⊗ D) (θ : D ⊗ H ⟶ W) (e : V ⊗ W ⟶ T)
    (a : C ⊗ T ⟶ B) (v : V' ⟶ V) :
    ((O ◁ v) ▷ H) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly d θ e a =
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly d θ ((v ▷ W) ≫ e) a := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly_post d θ ((v ▷ W) ≫ e) a e a v (𝟙 T) (𝟙 B)
    (by simp only [Category.comp_id])
    (by simp only [whiskerLeft_id, Category.id_comp, Category.comp_id])
  simpa only [Category.comp_id] using h

/-- 概要：組み立ての係数の射を分配・余演算・作用へ移す（BF §3.1）。
方針：一般の自然性で入力・評価点・中間出力・最終出力を固定する。
規約：三つの係数の射は同型である必要はない。
使われ方：Hopf 対角の部分合成保存を convolution の組み立てへ適用する。 -/
lemma convolutionAssembly_coefficient {O C D O' C' D' V H W T B : K}
    (d : O ⟶ C ⊗ D) (θ : D ⊗ H ⟶ W) (e : V ⊗ W ⟶ T) (a : C ⊗ T ⟶ B)
    (d' : O' ⟶ C' ⊗ D') (θ' : D' ⊗ H ⟶ W) (a' : C' ⊗ T ⟶ B)
    (f : O ⟶ O') (c : C ⟶ C') (g : D ⟶ D')
    (hd : f ≫ d' = d ≫ (c ⊗ₘ g)) (hθ : (g ▷ H) ≫ θ' = θ)
    (ha : (c ▷ T) ≫ a' = a) :
    (f ▷ V ▷ H) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly d' θ' e a' = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly d θ e a := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly_naturality d θ e a d' θ' e a'
    f c g (𝟙 V) (𝟙 H) (𝟙 W) (𝟙 T) (𝟙 B) hd
    (by simpa only [tensorHom_id, Category.comp_id] using hθ)
    (by simp only [tensorHom_id, id_whiskerRight, Category.id_comp, Category.comp_id])
    (by simpa only [tensorHom_id, Category.comp_id] using ha)
  simpa only [tensorHom_id, Category.comp_id] using h

/-- 概要：係数の部分合成と入力代入の評価から二段の合成則が従う（BF §3.1）。
方針：係数の自然性、二段の組み立ての合成、入力への自然性を連結する。
規約：全ての射は一般の対称モノイダル圏で指定する。
使われ方：複体への特殊化での大きな構造射の展開を避けて convolution 合成則を得る。 -/
lemma convolutionAssembly_composition_of_maps
    {O C D Q E F V V' H W Z T Y B O' C' D' : K}
    (d : O ⟶ C ⊗ D) (q : Q ⟶ E ⊗ F)
    (θ : D ⊗ H ⟶ W) (ψ : F ⊗ W ⟶ Z) (e : V ⊗ Z ⟶ T)
    (a : E ⊗ T ⟶ Y) (b : C ⊗ Y ⟶ B)
    (d' : O' ⟶ C' ⊗ D') (θ' : D' ⊗ H ⟶ Z) (a' : C' ⊗ T ⟶ B)
    (f : O ⊗ Q ⟶ O') (c : C ⊗ E ⟶ C') (g : D ⊗ F ⟶ D')
    (e' : V' ⊗ W ⟶ Y) (v : Q ⊗ V ⟶ V')
    (hd : f ≫ d' = ((d ⊗ₘ q) ≫ tensorμ C D E F) ≫ (c ⊗ₘ g))
    (hθ : (g ▷ H) ≫ θ' =
      ((β_ D F).hom ▷ H) ≫ (α_ F D H).hom ≫ (F ◁ θ) ≫ ψ)
    (ha : (c ▷ T) ≫ a' = (α_ C E T).hom ≫ (C ◁ a) ≫ b)
    (hv : (v ▷ W) ≫ e' = _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly q ψ e a) :
    (f ▷ V ▷ H) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly d' θ' e a' =
      ((α_ O Q V).hom ▷ H) ≫ ((O ◁ v) ▷ H) ≫ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly d θ e' b := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly_input, hv]
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly_coefficient _ _ e _ d' θ' a' f c g hd hθ ha).trans
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly_composition d q θ ψ e a b).symm

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
