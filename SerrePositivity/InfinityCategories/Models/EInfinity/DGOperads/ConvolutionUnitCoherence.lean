module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.ConvolutionUnitEvaluation
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
模型。文献の定義との比較は後で
# Convolution の単位の図式

概要：Berger–Fresse §3.1 の convolution の単位則を対称モノイダル圏の射で比較する。
方針：対角の単位と四因子の交換を単位子へ縮約する。
規約：複体の次数に依存しない一般の図式として証明する。
使われ方：Hopf 対角と代数・余代数の単位則を convolution へ移す。
-/

@[expose] public section

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory

variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [SymmetricCategory C]

/-- 概要：単位の対角の後の分離は評価点への単位の挿入である（BF §3.1）。
方針：tensorμ の単位との交換を展開しモノイダル整合性で比較する。
規約：前方の入力対象 V と評価点 H は任意。
使われ方：convolution の単位で余代数の単位則を適用する。 -/
@[reassoc]
lemma convolutionUnitDiagonal (V H : C) :
    (((λ_ (𝟙_ C)).inv ▷ V) ▷ H) ≫ (α_ (𝟙_ C ⊗ 𝟙_ C) V H).hom ≫
      tensorμ (𝟙_ C) (𝟙_ C) V H =
      ((𝟙_ C ⊗ V) ◁ (λ_ H).inv) := by
  simp only [tensorμ, braiding_tensorUnit_left,
    comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  monoidal


/-- 概要：分離後の convolution の単位は評価の単位になる（BF §3.1）。
方針：余演算の単位で評価点を縮約し、作用の単位と一次評価を順に適用する。
規約：一次冪の比較を任意の同型 v,w,t として明示する。
使われ方：複体の convolution の単位公理の一般の図式計算となる。 -/
lemma convolutionUnitAssembly {O V F H W T B : C} (u : 𝟙_ C ⟶ O)
    (v : V ≅ F) (w : W ≅ H) (t : T ≅ B)
    (θ : O ⊗ H ⟶ W) (a : O ⊗ T ⟶ B) (e : V ⊗ W ⟶ T) (ev : F ⊗ H ⟶ B)
    (hθ : (u ▷ H) ≫ θ ≫ w.hom = (λ_ H).hom)
    (ha : (u ▷ T) ≫ a = (λ_ T).hom ≫ t.hom)
    (he : e ≫ t.hom = (v.hom ⊗ₘ w.hom) ≫ ev) :
    (((λ_ (𝟙_ C)).inv ▷ V) ▷ H) ≫ (α_ (𝟙_ C ⊗ 𝟙_ C) V H).hom ≫
      tensorμ (𝟙_ C) (𝟙_ C) V H ≫ ((u ▷ V) ⊗ₘ (u ▷ H)) ≫
      ((O ⊗ V) ◁ θ) ≫ (α_ O V W).hom ≫ (O ◁ e) ≫ a =
    ((λ_ V).hom ▷ H) ≫ (v.hom ▷ H) ≫ ev := by
  have hθ' : (λ_ H).inv ≫ (u ▷ H) ≫ θ = w.inv := by
    apply (cancel_mono w.hom).1
    simp only [Category.assoc, hθ, Iso.inv_hom_id]
  have he' : (V ◁ w.inv) ≫ e ≫ t.hom = (v.hom ▷ H) ≫ ev := by
    rw [he, tensorHom_def']
    simp only [← Category.assoc, ← whiskerLeft_comp, Iso.inv_hom_id,
      whiskerLeft_id, Category.id_comp]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionUnitDiagonal_assoc, tensorHom_def]
  simp only [Category.assoc]
  rw [whisker_exchange_assoc]
  simp only [← whiskerLeft_comp_assoc]
  rw [hθ', associator_naturality_right_assoc, associator_naturality_left_assoc]
  simp only [← whiskerLeft_comp_assoc]
  rw [← whisker_exchange_assoc, ha, leftUnitor_naturality_assoc]
  simp only [Category.assoc]
  rw [he']
  monoidal


/-- 概要：単位を保つ対角を含む convolution 図式は単位則を満たす（BF §3.1）。
方針：対角の単位保存を自然性で分離した後、単位の組み立て公式を適用する。
規約：一次冪の比較は任意の同型として扱う。
使われ方：実際の Hopf オペラッドの convolution の単位則へ特殊化する。 -/
lemma convolutionUnitLaw {O V F H W T B : C} (u : 𝟙_ C ⟶ O) (d : O ⟶ O ⊗ O)
    (v : V ≅ F) (w : W ≅ H) (t : T ≅ B)
    (θ : O ⊗ H ⟶ W) (a : O ⊗ T ⟶ B) (e : V ⊗ W ⟶ T) (ev : F ⊗ H ⟶ B)
    (hd : u ≫ d = (λ_ (𝟙_ C)).inv ≫ (u ⊗ₘ u))
    (hθ : (u ▷ H) ≫ θ ≫ w.hom = (λ_ H).hom)
    (ha : (u ▷ T) ≫ a = (λ_ T).hom ≫ t.hom)
    (he : e ≫ t.hom = (v.hom ⊗ₘ w.hom) ≫ ev) :
    ((u ▷ V) ▷ H) ≫ ((d ▷ V) ▷ H) ≫ (α_ (O ⊗ O) V H).hom ≫
      tensorμ O O V H ≫ ((O ⊗ V) ◁ θ) ≫ (α_ O V W).hom ≫ (O ◁ e) ≫ a =
      ((λ_ V).hom ▷ H) ≫ (v.hom ▷ H) ≫ ev := by
  rw [← comp_whiskerRight_assoc, ← comp_whiskerRight, hd]
  simp only [comp_whiskerRight, Category.assoc]
  rw [associator_naturality_left_assoc, tensorμ_natural_left_assoc]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.convolutionUnitAssembly u v w t θ a e ev hθ ha he

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
