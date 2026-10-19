module

public import SerrePositivity.EInfinity.Operad.CoInsertion
public import SerrePositivity.EInfinity.Operad.UnitPowers

/-!
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

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.TensorPowers

private def coBlock {K : Type u} [Category.{v} K] [MonoidalCategory K]
    [SymmetricCategory K] (C L M X Y : K) (θ : C ⊗ X ⟶ Y) :
    C ⊗ (L ⊗ (X ⊗ M)) ⟶ L ⊗ (Y ⊗ M) :=
  (α_ C L (X ⊗ M)).inv ≫ ((β_ C L).hom ▷ (X ⊗ M)) ≫
    (α_ L C (X ⊗ M)).hom ≫ (L ◁ (α_ C X M).inv) ≫ (L ◁ (θ ▷ M))

private lemma block_natural {K : Type u} [Category.{v} K] [MonoidalCategory K]
    [SymmetricCategory K] {C L M X Y L' M' X' Y' : K}
    (l : L ⟶ L') (m : M ⟶ M') (x : X ⟶ X') (y : Y ⟶ Y')
    (θ : C ⊗ X ⟶ Y) (θ' : C ⊗ X' ⟶ Y') (hθ : (C ◁ x) ≫ θ' = θ ≫ y) :
    (C ◁ (l ⊗ₘ (x ⊗ₘ m))) ≫ coBlock C L' M' X' Y' θ' =
      coBlock C L M X Y θ ≫ (l ⊗ₘ (y ⊗ₘ m)) := by
  unfold coBlock
  rw [← id_tensorHom, associator_inv_naturality_assoc]
  rw [tensorHom_comp_whiskerRight_assoc, BraidedCategory.braiding_naturality]
  rw [← whiskerRight_comp_tensorHom_assoc, associator_naturality_assoc]
  simp only [id_tensorHom]
  rw [tensorHom_comp_whiskerLeft_assoc]
  rw [← id_tensorHom C (x ⊗ₘ m), associator_inv_naturality]
  simp only [Category.assoc, ← id_tensorHom, ← tensorHom_id,
    tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  simp only [← id_tensorHom] at hθ
  rw [hθ]

private lemma block_unit {K : Type u} [Category.{v} K] [MonoidalCategory K]
    [SymmetricCategory K] {C : K} (φ : C ⊗ (𝟙_ K) ⟶ 𝟙_ K) :
    coBlock C (𝟙_ K) (𝟙_ K) (𝟙_ K) (𝟙_ K) φ ≫
      ((𝟙_ K) ◁ (λ_ (𝟙_ K)).hom) ≫ (λ_ (𝟙_ K)).hom =
    (C ◁ (((𝟙_ K) ◁ (λ_ (𝟙_ K)).hom) ≫ (λ_ (𝟙_ K)).hom)) ≫ φ := by
  unfold coBlock
  rw [braiding_tensorUnit_right]
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  monoidal

private lemma block_contract {K : Type u} [Category.{v} K] [MonoidalCategory K]
    [SymmetricCategory K] {C L M N : K} (p : L ⟶ 𝟙_ K) (q : M ⟶ 𝟙_ K)
    (r : N ⟶ 𝟙_ K) (θ : C ⊗ (𝟙_ K) ⟶ N) :
    coBlock C L M (𝟙_ K) N θ ≫ (p ⊗ₘ (r ⊗ₘ q)) ≫
      ((𝟙_ K) ◁ (λ_ (𝟙_ K)).hom) ≫ (λ_ (𝟙_ K)).hom =
    (C ◁ ((p ⊗ₘ ((𝟙_ K) ◁ q)) ≫ ((𝟙_ K) ◁ (λ_ (𝟙_ K)).hom) ≫
      (λ_ (𝟙_ K)).hom)) ≫ θ ≫ r := by
  have hn := congrArg (fun f => f ≫ ((𝟙_ K) ◁ (λ_ (𝟙_ K)).hom) ≫
    (λ_ (𝟙_ K)).hom) (block_natural p q (𝟙 (𝟙_ K)) r θ (θ ≫ r)
      (by simp only [whiskerLeft_id, Category.id_comp]))
  simp only [Category.assoc] at hn
  rw [block_unit] at hn
  simpa only [id_tensorHom, whiskerLeft_comp, Category.assoc] using hn.symm

/-- 概要：単位冪を二列へ分けた後の縮約は元の縮約に一致する（BF §3.1）。
方針：連結と縮約の公式へ連結の逆射を合成する。
規約：空の列を含む。
使われ方：余代入の入力に現れる列の分割を消す。 -/
@[reassoc]
lemma tensorUnitPowerIso_split (K : Type u) [Category.{v} K] [MonoidalCategory K]
    (m n : ℕ) :
    (appendIso (𝟙_ K) m n).inv ≫
      ((tensorUnitPowerIso K m).hom ⊗ₘ (tensorUnitPowerIso K n).hom) ≫
      (λ_ (𝟙_ K)).hom = (tensorUnitPowerIso K (m + n)).hom := by
  rw [← tensorUnitPowerIso_append]
  simp only [Iso.inv_hom_id_assoc]

variable {A : Type u} [CommRing A]

attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct
attribute [local implicit_reducible] TensorPowers.power

/-- 概要：単位出力への余代入は全出力の縮約後には同じ余演算となる（BF §3.1）。
方針：前後の列の縮約にブロックの自然性を適用し、単位子を消去する。
規約：任意の出力位置と出力数零を扱う。
使われ方：単位余代数の全位置での合成則を証明する。 -/
@[reassoc]
lemma tensorCoInsertionAction_unit (C : Complex A) (m n : ℕ) (i : Fin (m + 1))
    (θ : C ⊗ (𝟙_ (Complex A)) ⟶ power (𝟙_ (Complex A)) n) :
    tensorCoInsertionAction (𝟙_ (Complex A)) C m n i θ ≫
      (tensorUnitPowerIso (Complex A) (m + n)).hom =
    (C ◁ (tensorUnitPowerIso (Complex A) (m + 1)).hom) ≫ θ ≫
      (tensorUnitPowerIso (Complex A) n).hom := by
  unfold tensorCoInsertionAction
  dsimp only
  simp only [Category.assoc]
  rw [tensorUnitPowerIso_index (Complex A)
    (show i.val + (n + (m - i.val)) = m + n by omega), tensorUnitPowerIso_append]
  rw [whiskerLeft_comp_tensorHom_assoc, tensorUnitPowerIso_append]
  rw [← tensorHom_comp_whiskerLeft_assoc]
  have hb := block_contract
    (tensorUnitPowerIso (Complex A) i.val).hom
    (tensorUnitPowerIso (Complex A) (m - i.val)).hom
    (tensorUnitPowerIso (Complex A) n).hom θ
  simp only [coBlock, Category.assoc] at hb
  erw [hb]
  simp only [← whiskerLeft_comp_assoc]
  rw [tensorHom_comp_whiskerLeft_assoc]
  simp only [Category.assoc]
  change (C ◁ (_ ≫ (appendIso (𝟙_ (Complex A)) i.val (m - i.val + 1)).inv ≫
    ((tensorUnitPowerIso (Complex A) i.val).hom ⊗ₘ
      (tensorUnitPowerIso (Complex A) (m - i.val + 1)).hom) ≫
        (λ_ (𝟙_ (Complex A))).hom)) ≫ θ ≫ _ = _
  rw [tensorUnitPowerIso_split, tensorUnitPowerIso_index (Complex A)
    (show m + 1 = i.val + (m - i.val + 1) by omega)]

end SerrePositivity.EInfinity
