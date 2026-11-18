module

public import SerrePositivity.HomologicalAlgebra.Complexes.NegativeTensor.Comparison

/-!
# テンソル比較の自然性

概要：Berger–Fresse §1.1 の次数変更とテンソルの比較が二つの複体に自然であることを示す。
方針：負の全次数で各直和因子を比較し、正次数は零対象で処理する。
規約：鎖写像を同じ次数埋め込みで延長する。
使われ方：AW 対角の自然性と Σ_n 同変性を整数模型へ移す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.NegativeTensor

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex

variable {A : Type u} [CommRing A]

/-- 概要：延長した鎖写像の負次数での成分（Berger–Fresse §1.1）。
方針：次数埋め込みに沿う延長の射の公式を使う。
規約：次数 n と −n の比較同型を明示する。
使われ方：テンソル比較と AW 対角の自然性。 -/
lemma extendMap_f_neg {K L : ChainComplex (ModuleCat.{u} A) ℕ} (f : K ⟶ L) (n : ℕ) :
    (extendMap f ComplexShape.embeddingDownNat).f (-(n : ℤ)) =
      (_root_.SerrePositivity.NegativeTensor.xIso K n).hom ≫ f.f n ≫ (_root_.SerrePositivity.NegativeTensor.xIso L n).inv :=
  HomologicalComplex.extendMap_f f ComplexShape.embeddingDownNat rfl

/-- 概要：標準同型の逆は延長した鎖写像と可換（Berger–Fresse §1.1）。
方針：延長した射の成分公式で同型と逆同型を消す。
規約：任意の自然数次数を扱う。
使われ方：テンソル比較の成分ごとの自然性。 -/
@[reassoc (attr := simp)]
lemma xIso_inv_extendMap {K L : ChainComplex (ModuleCat.{u} A) ℕ} (f : K ⟶ L) (n : ℕ) :
    (_root_.SerrePositivity.NegativeTensor.xIso K n).inv ≫ (extendMap f ComplexShape.embeddingDownNat).f (-(n : ℤ)) =
      f.f n ≫ (_root_.SerrePositivity.NegativeTensor.xIso L n).inv := by
  rw [_root_.SerrePositivity.NegativeTensor.extendMap_f_neg]
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]

private lemma ι_natTensorHom {K L K' L' : ChainComplex (ModuleCat.{u} A) ℕ}
    (f : K ⟶ K') (g : L ⟶ L') (n p q : ℕ) (h : p + q = n) :
    ιTensorObj K L p q n h ≫ (HomologicalComplex.tensorHom f g).f n =
      (f.f p ⊗ₘ g.f q) ≫ ιTensorObj K' L' p q n h := by
  rw [ι_mapBifunctorMap]
  change (f.f p ▷ L.X q) ≫ (K'.X p ◁ g.f q) ≫ _ = _
  rw [MonoidalCategory.tensorHom_def, Category.assoc]

private lemma ι_natTensorHom_assoc {K L K' L' : ChainComplex (ModuleCat.{u} A) ℕ}
    (f : K ⟶ K') (g : L ⟶ L') (n p q : ℕ) (h : p + q = n)
    {T : ModuleCat.{u} A} (v : (HomologicalComplex.tensorObj K' L').X n ⟶ T) :
    ιTensorObj K L p q n h ≫ (HomologicalComplex.tensorHom f g).f n ≫ v =
      (f.f p ⊗ₘ g.f q) ≫ ιTensorObj K' L' p q n h ≫ v := by
  rw [← Category.assoc, _root_.SerrePositivity.NegativeTensor.ι_natTensorHom, Category.assoc]

/-- 概要：テンソルの負次数比較は鎖写像の対に自然（Berger–Fresse §1.1）。
方針：各直和因子に制限し標準同型の自然性を使う。
規約：左右の鎖写像は独立に選べる。
使われ方：次数比較を複体上の自然同型にする。 -/
lemma degreeMap_natural {K L K' L' : ChainComplex (ModuleCat.{u} A) ℕ}
    (f : K ⟶ K') (g : L ⟶ L') (n : ℕ) :
    (HomologicalComplex.tensorHom f g).f n ≫ _root_.SerrePositivity.NegativeTensor.degreeMap K' L' n =
      _root_.SerrePositivity.NegativeTensor.degreeMap K L n ≫
        (HomologicalComplex.tensorHom (extendMap f ComplexShape.embeddingDownNat)
          (extendMap g ComplexShape.embeddingDownNat)).f (-(n : ℤ)) := by
  apply mapBifunctor.hom_ext
  intro p q hpq
  change p + q = n at hpq
  rw [_root_.SerrePositivity.NegativeTensor.ι_natTensorHom_assoc, _root_.SerrePositivity.NegativeTensor.ι_degreeMap, _root_.SerrePositivity.NegativeTensor.ι_degreeMap_assoc,
    SerrePositivity.ιTensorObj_cochainTensorMap]
  simp only [← Category.assoc, MonoidalCategory.tensorHom_comp_tensorHom, _root_.SerrePositivity.NegativeTensor.xIso_inv_extendMap]

/-- 概要：延長とテンソルの比較は複体の対に自然（Berger–Fresse §1.1）。
方針：正次数は零、負次数は直和比較の自然性に帰着する。
規約：比較は既存の整数テンソルの鎖写像と可換する。
使われ方：AW 対角の整数模型での自然性と同変性。 -/
lemma comparison_natural {K L K' L' : ChainComplex (ModuleCat.{u} A) ℕ}
    (f : K ⟶ K') (g : L ⟶ L') :
    extendMap (HomologicalComplex.tensorHom f g) ComplexShape.embeddingDownNat ≫
        (_root_.SerrePositivity.NegativeTensor.comparison K' L').hom =
      (_root_.SerrePositivity.NegativeTensor.comparison K L).hom ≫
        HomologicalComplex.tensorHom (extendMap f ComplexShape.embeddingDownNat)
          (extendMap g ComplexShape.embeddingDownNat) := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : 0 < i
  · exact (_root_.SerrePositivity.NegativeTensor.isZero_positive (HomologicalComplex.tensorObj K L) i hi).eq_of_src _ _
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = -(n : ℤ) := ⟨(-i).toNat, by omega⟩
  simp only [HomologicalComplex.comp_f, _root_.SerrePositivity.NegativeTensor.extendMap_f_neg, _root_.SerrePositivity.NegativeTensor.comparison_hom_f_neg,
    Category.assoc, Iso.inv_hom_id_assoc]
  rw [_root_.SerrePositivity.NegativeTensor.degreeMap_natural]

end SerrePositivity.NegativeTensor
