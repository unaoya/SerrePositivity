module

public import SerrePositivity.HomologicalAlgebra.Complexes.NegativeTensor.Associativity

/-!
# 余結合的な対角の負次数への移送

概要：Berger–Fresse §1.1.4 の余結合的鎖対角を整数コチェイン対角へ移す。
方針：延長とテンソルの比較の自然性・結合子との適合性を使う。
規約：元の対角の余結合性は既存の鎖複体の結合子で述べる。
使われ方：AW の余結合性を実際の E(n) の整数複体上で得る。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.NegativeTensor

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex

variable {A : Type u} [CommRing A]

/-- 概要：鎖複体の対角を負の整数コチェインへ移す（Berger–Fresse §1.1.4）。
方針：対角を延長しテンソル比較を後置する。
規約：入力の対角は任意の鎖写像でよい。
使われ方：一般の AW 対角の整数模型。 -/
def comultiplication (K : ChainComplex (ModuleCat.{u} A) ℕ)
    (d : K ⟶ HomologicalComplex.tensorObj K K) :
    _root_.SerrePositivity.NegativeTensor.extend K ⟶ HomologicalComplex.tensorObj (_root_.SerrePositivity.NegativeTensor.extend K) (_root_.SerrePositivity.NegativeTensor.extend K) :=
  extendMap d ComplexShape.embeddingDownNat ≫ (_root_.SerrePositivity.NegativeTensor.comparison K K).hom

private lemma tensorHom_comp_left
    {K L M N : CochainComplex (ModuleCat.{u} A) ℤ} (f : K ⟶ L) (g : L ⟶ M) :
    HomologicalComplex.tensorHom (f ≫ g) (𝟙 N) =
      HomologicalComplex.tensorHom f (𝟙 N) ≫ HomologicalComplex.tensorHom g (𝟙 N) := by
  change ((f ≫ g) ⊗ₘ 𝟙 N) = (f ⊗ₘ 𝟙 N) ≫ (g ⊗ₘ 𝟙 N)
  rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]

private lemma tensorHom_comp_right
    {K L M N : CochainComplex (ModuleCat.{u} A) ℤ} (f : K ⟶ L) (g : L ⟶ M) :
    HomologicalComplex.tensorHom (𝟙 N) (f ≫ g) =
      HomologicalComplex.tensorHom (𝟙 N) f ≫ HomologicalComplex.tensorHom (𝟙 N) g := by
  change (𝟙 N ⊗ₘ (f ≫ g)) = (𝟙 N ⊗ₘ f) ≫ (𝟙 N ⊗ₘ g)
  rw [MonoidalCategory.tensorHom_comp_tensorHom, Category.id_comp]

/-- 概要：対角の負次数への移送は余結合性を保つ（Berger–Fresse §1.1.4）。
方針：比較の自然性で二重対角をまとめ、結合子の比較と元の余結合性を使う。
規約：余結合性の等式に追加の同型や仮定を含めない。
使われ方：AW コチェイン対角の余結合性。 -/
lemma comultiplication_coassoc (K : ChainComplex (ModuleCat.{u} A) ℕ)
    (d : K ⟶ HomologicalComplex.tensorObj K K)
    (hd : d ≫ HomologicalComplex.tensorHom d (𝟙 K) ≫
        (HomologicalComplex.associator K K K).hom =
      d ≫ HomologicalComplex.tensorHom (𝟙 K) d) :
    _root_.SerrePositivity.NegativeTensor.comultiplication K d ≫
        HomologicalComplex.tensorHom (_root_.SerrePositivity.NegativeTensor.comultiplication K d) (𝟙 (_root_.SerrePositivity.NegativeTensor.extend K)) ≫
        (HomologicalComplex.associator (_root_.SerrePositivity.NegativeTensor.extend K) (_root_.SerrePositivity.NegativeTensor.extend K) (_root_.SerrePositivity.NegativeTensor.extend K)).hom =
      _root_.SerrePositivity.NegativeTensor.comultiplication K d ≫
        HomologicalComplex.tensorHom (𝟙 (_root_.SerrePositivity.NegativeTensor.extend K)) (_root_.SerrePositivity.NegativeTensor.comultiplication K d) := by
  let E := ComplexShape.embeddingDownNat
  have hl := _root_.SerrePositivity.NegativeTensor.comparison_natural d (𝟙 K)
  have hr := _root_.SerrePositivity.NegativeTensor.comparison_natural (𝟙 K) d
  simp only [extendMap_id] at hl hr
  simp only [_root_.SerrePositivity.NegativeTensor.comultiplication, _root_.SerrePositivity.NegativeTensor.tensorHom_comp_left, _root_.SerrePositivity.NegativeTensor.tensorHom_comp_right, Category.assoc]
  rw [← reassoc_of% hl]
  rw [_root_.SerrePositivity.NegativeTensor.comparison_associator]
  have he := congrArg (fun f => extendMap f E) hd
  simp only [extendMap_comp] at he
  rw [reassoc_of% he, reassoc_of% hr]

end SerrePositivity.NegativeTensor
