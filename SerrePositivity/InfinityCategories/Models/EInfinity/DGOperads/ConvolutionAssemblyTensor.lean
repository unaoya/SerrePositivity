module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionAssembly
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
模型。文献の定義との比較は後で
# Convolution 図式と後方ブロックの評価

概要：Berger–Fresse §3.1 の convolution の評価に、後方の独立な評価を連結する。
方針：四因子の分離と結合子の整合性で、後方の評価を組み立ての外へ出す。
規約：後方の二因子と評価は任意でよい。
使われ方：先頭ブロックの convolution の評価を任意の長さの入力列へ拡張する。
-/

@[expose] public section

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

variable {K : Type u} [Category.{v} K] [MonoidalCategory K] [SymmetricCategory K]

private lemma assembly_expand {O C D V H W T B : K} (d : O ⟶ C ⊗ D)
    (θ : D ⊗ H ⟶ W) (e : V ⊗ W ⟶ T) (a : C ⊗ T ⟶ B) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly d θ e a = ((d ▷ V) ▷ H) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly (𝟙 (C ⊗ D)) θ e a := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly, id_whiskerRight, Category.id_comp]

private lemma coaction_exchange {D R H W : K} (θ : D ⊗ H ⟶ W) :
    ((β_ D R).hom ▷ H) ≫ (α_ R D H).hom ≫ (R ◁ θ) ≫ (β_ R W).hom =
    (α_ D R H).hom ≫ (D ◁ (β_ R H).hom) ≫ (α_ D H R).inv ≫ (θ ▷ R) := by
  rw [BraidedCategory.braiding_naturality_right, BraidedCategory.braiding_tensor_right_hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← comp_whiskerRight_assoc, SymmetricCategory.symmetry]
  simp only [id_whiskerRight, Category.id_comp]

private lemma tensorRight_core {C D V H W T B R S L : K}
    (θ : D ⊗ H ⟶ W) (e : V ⊗ W ⟶ T) (a : C ⊗ T ⟶ B) (q : R ⊗ S ⟶ L) :
    ((α_ (C ⊗ D) V R).inv ▷ (H ⊗ S)) ≫ tensorμ ((C ⊗ D) ⊗ V) R H S ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly (𝟙 (C ⊗ D)) θ e a ⊗ₘ q) =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly (𝟙 (C ⊗ D)) ((α_ D H S).inv ≫ (θ ▷ S))
      (tensorμ V R W S ≫ (e ⊗ₘ q)) ((α_ C T L).inv ≫ (a ▷ L)) := by
  let N : ((C ⊗ D) ⊗ (V ⊗ R)) ⊗ (H ⊗ S) ⟶ B ⊗ L :=
    𝟙 _ ⊗≫ ((C ◁ (β_ D V).hom) ⊗ₘ ((β_ R H).hom ▷ S)) ⊗≫
      (C ◁ (V ◁ (θ ▷ R ▷ S))) ⊗≫ ((C ◁ e) ▷ (R ⊗ S)) ⊗≫ (a ⊗ₘ q)
  let N' : ((C ⊗ D) ⊗ (V ⊗ R)) ⊗ (H ⊗ S) ⟶ B ⊗ L :=
    𝟙 _ ⊗≫ ((C ◁ (β_ D V).hom) ▷ ((R ⊗ H) ⊗ S)) ⊗≫
      (C ◁ (V ◁ ((((β_ D R).hom ▷ H) ≫ (α_ R D H).hom ≫
        (R ◁ θ) ≫ (β_ R W).hom) ▷ S))) ⊗≫
      ((C ◁ e) ▷ (R ⊗ S)) ⊗≫ (a ⊗ₘ q)
  calc
    _ = N := by
      dsimp only [N]
      rw [tensorHom_def' (C ◁ (β_ D V).hom) ((β_ R H).hom ▷ S), tensorHom_def a q]
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly, tensorμ, tensorHom_def, id_whiskerRight,
        Category.id_comp, comp_whiskerRight, Category.assoc]
      monoidal
    _ = N' := by
      dsimp only [N, N']
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.coaction_exchange]
      simp only [tensorHom_def, comp_whiskerRight, whiskerLeft_comp]
      monoidal
    _ = _ := by
      dsimp only [N']
      rw [tensorHom_def' a q, tensorHom_def e q]
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly, tensorμ, id_whiskerRight, Category.id_comp,
        comp_whiskerRight, whiskerLeft_comp, Category.assoc,
        BraidedCategory.braiding_tensor_right_hom]
      monoidal

/-- 概要：独立な後方の評価をテンソルした convolution の図式（BF §3.1）。
方針：tensorμ と結合子の自然性を使い、後方の射を各段へ通す。
規約：係数の対角・余演算・評価・作用は任意の射として扱う。
使われ方：convolution の先頭位置の部分合成則を二ブロックの評価で検証する。 -/
lemma convolutionAssembly_tensorRight {O C D V H W T B R S L : K}
    (d : O ⟶ C ⊗ D) (θ : D ⊗ H ⟶ W) (e : V ⊗ W ⟶ T) (a : C ⊗ T ⟶ B)
    (q : R ⊗ S ⟶ L) :
    ((α_ O V R).inv ▷ (H ⊗ S)) ≫ tensorμ (O ⊗ V) R H S ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly d θ e a ⊗ₘ q) =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly d ((α_ D H S).inv ≫ (θ ▷ S))
      (tensorμ V R W S ≫ (e ⊗ₘ q)) ((α_ C T L).inv ≫ (a ▷ L)) := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorRight_core θ e a q
  have hμ := tensorμ_natural_left (d ▷ V) (𝟙 R) H S
  simp only [id_whiskerRight, tensorHom_id] at hμ
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.assembly_expand d θ e a, tensorHom_def, comp_whiskerRight]
  simp only [Category.assoc]
  rw [← reassoc_of% hμ, ← comp_whiskerRight_assoc,
    ← associator_inv_naturality_left, comp_whiskerRight]
  simp only [Category.assoc]
  rw [← tensorHom_def (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionAssembly (𝟙 (C ⊗ D)) θ e a) q, h]
  exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.assembly_expand d _ _ _).symm

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
