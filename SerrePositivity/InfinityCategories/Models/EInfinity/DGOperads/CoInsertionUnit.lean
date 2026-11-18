module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.CoInsertion
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.InsertionBlockNaturality
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.UnitPowers

/-!
模型。文献の定義との比較は後で
# 単位対象の出力列への余代入

概要：Berger–Fresse §3.1 の単位余代数の余代入を単位冪の縮約で計算する。
方針：前後の単位ブロックを縮約し、係数との交換を単位子で消す。
規約：任意の出力位置と零出力の余演算を含む。
使われ方：augmentation からの単位余代数の合成公理を証明する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe v u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers

private lemma block_unit {K : Type u} [Category.{v} K] [MonoidalCategory K]
    [SymmetricCategory K] {C : K} (φ : C ⊗ (𝟙_ K) ⟶ 𝟙_ K) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionBlock C (𝟙_ K) (𝟙_ K) (𝟙_ K) (𝟙_ K) φ ≫
      ((𝟙_ K) ◁ (λ_ (𝟙_ K)).hom) ≫ (λ_ (𝟙_ K)).hom =
    (C ◁ (((𝟙_ K) ◁ (λ_ (𝟙_ K)).hom) ≫ (λ_ (𝟙_ K)).hom)) ≫ φ := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionBlock
  rw [braiding_tensorUnit_right]
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  monoidal

private lemma block_contract {K : Type u} [Category.{v} K] [MonoidalCategory K]
    [SymmetricCategory K] {C L M N : K} (p : L ⟶ 𝟙_ K) (q : M ⟶ 𝟙_ K)
    (r : N ⟶ 𝟙_ K) (θ : C ⊗ (𝟙_ K) ⟶ N) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionBlock C L M (𝟙_ K) N θ ≫ (p ⊗ₘ (r ⊗ₘ q)) ≫
      ((𝟙_ K) ◁ (λ_ (𝟙_ K)).hom) ≫ (λ_ (𝟙_ K)).hom =
    (C ◁ ((p ⊗ₘ ((𝟙_ K) ◁ q)) ≫ ((𝟙_ K) ◁ (λ_ (𝟙_ K)).hom) ≫
      (λ_ (𝟙_ K)).hom)) ≫ θ ≫ r := by
  have hn := congrArg (fun f => f ≫ ((𝟙_ K) ◁ (λ_ (𝟙_ K)).hom) ≫
    (λ_ (𝟙_ K)).hom) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionBlock_naturality p q (𝟙 (𝟙_ K)) r θ (θ ≫ r)
      (by simp only [whiskerLeft_id, Category.id_comp]))
  simp only [Category.assoc] at hn
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.block_unit] at hn
  simpa only [id_tensorHom, whiskerLeft_comp, Category.assoc] using hn.symm

/-- 概要：単位冪を二列へ分けた後の縮約は元の縮約に一致する（BF §3.1）。
方針：連結と縮約の公式へ連結の逆射を合成する。
規約：空の列を含む。
使われ方：余代入の入力に現れる列の分割を消す。 -/
@[reassoc]
lemma tensorUnitPowerIso_split (K : Type u) [Category.{v} K] [MonoidalCategory K]
    (m n : ℕ) :
    (appendIso (𝟙_ K) m n).inv ≫
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso K m).hom ⊗ₘ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso K n).hom) ≫
      (λ_ (𝟙_ K)).hom = (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso K (m + n)).hom := by
  rw [← _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso_append]
  simp only [Iso.inv_hom_id_assoc]

variable {A : Type u} [CommRing A]

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] _root_.SerrePositivity.TensorPowers.power

/-- 概要：単位出力への余代入は全出力の縮約後には同じ余演算となる（BF §3.1）。
方針：前後の列の縮約にブロックの自然性を適用し、単位子を消去する。
規約：任意の出力位置と出力数零を扱う。
使われ方：単位余代数の全位置での合成則を証明する。 -/
@[reassoc]
lemma tensorCoInsertionAction_unit (C : Complex A) (m n : ℕ) (i : Fin (m + 1))
    (θ : C ⊗ (𝟙_ (Complex A)) ⟶ power (𝟙_ (Complex A)) n) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorCoInsertionAction (𝟙_ (Complex A)) C m n i θ ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso (Complex A) (m + n)).hom =
    (C ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso (Complex A) (m + 1)).hom) ≫ θ ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso (Complex A) n).hom := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorCoInsertionAction
  dsimp only
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso_index (Complex A)
    (show i.val + (n + (m - i.val)) = m + n by omega), _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso_append]
  rw [whiskerLeft_comp_tensorHom_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso_append]
  rw [← tensorHom_comp_whiskerLeft_assoc]
  have hb := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.block_contract
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso (Complex A) i.val).hom
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso (Complex A) (m - i.val)).hom
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso (Complex A) n).hom θ
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorInsertionBlock, Category.assoc] at hb
  erw [hb]
  simp only [← whiskerLeft_comp_assoc]
  rw [tensorHom_comp_whiskerLeft_assoc]
  simp only [Category.assoc]
  change (C ◁ (_ ≫ (appendIso (𝟙_ (Complex A)) i.val (m - i.val + 1)).inv ≫
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso (Complex A) i.val).hom ⊗ₘ
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso (Complex A) (m - i.val + 1)).hom) ≫
        (λ_ (𝟙_ (Complex A))).hom)) ≫ θ ≫ _ = _
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso_split, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorUnitPowerIso_index (Complex A)
    (show m + 1 = i.val + (m - i.val + 1) by omega)]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
