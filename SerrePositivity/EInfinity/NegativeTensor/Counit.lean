module

public import SerrePositivity.EInfinity.NegativeTensor.Comultiplication
public import SerrePositivity.EInfinity.NegativeTensor.Unit

/-!
# 余単位則の負次数への移送

概要：Berger–Fresse §1.1.4 の鎖対角の左右余単位則を整数模型へ移す。
方針：比較の自然性と左右単位子との適合性を使う。
規約：augmentation の終域は対応するテンソル単位。
使われ方：AW と Barratt–Eccles の整数対角の余単位則。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.NegativeTensor

open CategoryTheory MonoidalCategory HomologicalComplex

variable {A : Type u} [CommRing A]

/-- 概要：鎖 augmentation の負次数への移送（Berger–Fresse §1.1.4）。
方針：射を延長し単位の標準比較を後置する。
規約：終域は整数コチェインの単位。
使われ方：移送した対角の余単位を指定する。 -/
def augmentation (K : ChainComplex (ModuleCat.{u} A) ℕ)
    (c : K ⟶ HomologicalComplex.tensorUnit (ModuleCat A) (.down ℕ)) :
    extend K ⟶ HomologicalComplex.tensorUnit (ModuleCat A) (.up ℤ) :=
  extendMap c ComplexShape.embeddingDownNat ≫ (unitComparison (A := A)).hom

/-- 概要：負次数への移送は左余単位則を保つ（Berger–Fresse §1.1.4）。
方針：元の左余単位則を左単位子の逆への等式に直して比較の自然性を使う。
規約：元の鎖対角と augmentation は任意に指定できる。
使われ方：整数 AW 対角の左余単位則。 -/
lemma comultiplication_left_counit (K : ChainComplex (ModuleCat.{u} A) ℕ)
    (d : K ⟶ HomologicalComplex.tensorObj K K)
    (c : K ⟶ HomologicalComplex.tensorUnit (ModuleCat A) (.down ℕ))
    (hc : d ≫ HomologicalComplex.tensorHom c (𝟙 K) ≫
      (HomologicalComplex.leftUnitor K).hom = 𝟙 K) :
    comultiplication K d ≫
        HomologicalComplex.tensorHom (augmentation K c) (𝟙 (extend K)) ≫
        (HomologicalComplex.leftUnitor (extend K)).hom = 𝟙 _ := by
  have hc' : d ≫ HomologicalComplex.tensorHom c (𝟙 K) =
      (HomologicalComplex.leftUnitor K).inv := by
    apply (cancel_mono (HomologicalComplex.leftUnitor K).hom).1
    simpa only [Category.assoc, Iso.inv_hom_id] using hc
  have hn := comparison_natural c (𝟙 K)
  simp only [extendMap_id] at hn
  have ht : HomologicalComplex.tensorHom (augmentation K c) (𝟙 (extend K)) =
      HomologicalComplex.tensorHom (extendMap c ComplexShape.embeddingDownNat) (𝟙 (extend K)) ≫
        HomologicalComplex.tensorHom (unitComparison (A := A)).hom (𝟙 (extend K)) := by
    change ((extendMap c ComplexShape.embeddingDownNat ≫ (unitComparison (A := A)).hom) ⊗ₘ
        𝟙 (extend K)) =
      (extendMap c ComplexShape.embeddingDownNat ⊗ₘ 𝟙 (extend K)) ≫
        ((unitComparison (A := A)).hom ⊗ₘ 𝟙 (extend K))
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]
  rw [ht]
  simp only [comultiplication, Category.assoc]
  rw [← reassoc_of% hn,
    ← reassoc_of% (extendMap_comp d (HomologicalComplex.tensorHom c (𝟙 K))
      ComplexShape.embeddingDownNat), hc']
  rw [reassoc_of% (comparison_leftUnitor K), Iso.inv_hom_id]

/-- 概要：負次数への移送は右余単位則を保つ（Berger–Fresse §1.1.4）。
方針：元の右余単位則を右単位子の逆への等式に直して比較の自然性を使う。
規約：元の鎖対角と augmentation は任意に指定できる。
使われ方：整数 AW 対角の右余単位則。 -/
lemma comultiplication_right_counit (K : ChainComplex (ModuleCat.{u} A) ℕ)
    (d : K ⟶ HomologicalComplex.tensorObj K K)
    (c : K ⟶ HomologicalComplex.tensorUnit (ModuleCat A) (.down ℕ))
    (hc : d ≫ HomologicalComplex.tensorHom (𝟙 K) c ≫
      (HomologicalComplex.rightUnitor K).hom = 𝟙 K) :
    comultiplication K d ≫
        HomologicalComplex.tensorHom (𝟙 (extend K)) (augmentation K c) ≫
        (HomologicalComplex.rightUnitor (extend K)).hom = 𝟙 _ := by
  have hc' : d ≫ HomologicalComplex.tensorHom (𝟙 K) c =
      (HomologicalComplex.rightUnitor K).inv := by
    apply (cancel_mono (HomologicalComplex.rightUnitor K).hom).1
    simpa only [Category.assoc, Iso.inv_hom_id] using hc
  have hn := comparison_natural (𝟙 K) c
  simp only [extendMap_id] at hn
  have ht : HomologicalComplex.tensorHom (𝟙 (extend K)) (augmentation K c) =
      HomologicalComplex.tensorHom (𝟙 (extend K)) (extendMap c ComplexShape.embeddingDownNat) ≫
        HomologicalComplex.tensorHom (𝟙 (extend K)) (unitComparison (A := A)).hom := by
    change (𝟙 (extend K) ⊗ₘ
        (extendMap c ComplexShape.embeddingDownNat ≫ (unitComparison (A := A)).hom)) =
      (𝟙 (extend K) ⊗ₘ extendMap c ComplexShape.embeddingDownNat) ≫
        (𝟙 (extend K) ⊗ₘ (unitComparison (A := A)).hom)
    rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]
  rw [ht]
  simp only [comultiplication, Category.assoc]
  rw [← reassoc_of% hn,
    ← reassoc_of% (extendMap_comp d (HomologicalComplex.tensorHom (𝟙 K) c)
      ComplexShape.embeddingDownNat), hc']
  rw [reassoc_of% (comparison_rightUnitor K), Iso.inv_hom_id]

end SerrePositivity.EInfinity.NegativeTensor
