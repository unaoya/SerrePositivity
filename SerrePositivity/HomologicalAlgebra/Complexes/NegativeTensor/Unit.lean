module

public import SerrePositivity.HomologicalAlgebra.Complexes.NegativeTensor.Associativity

/-!
# 負次数テンソル比較と単位子

概要：Berger–Fresse §1.1 の次数変更がテンソル単位を保つことを明示する。
方針：単一複体の延長同型と、単位子の直和包含での公式を使う。
規約：鎖複体と整数コチェイン複体の既存の単位を用いる。
使われ方：AW の左右余単位則を整数模型へ移す。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.NegativeTensor

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.CategoryTheory.MonoidalCategory _root_.HomologicalComplex
open scoped _root_.TensorProduct

variable {A : Type u} [CommRing A]

/-- 概要：零延長した鎖テンソル単位と整数テンソル単位の同型（Berger–Fresse §1.1）。
方針：次数零の単一複体の延長同型を使う。
規約：両単位とも係数環を次数零に置く。
使われ方：整数 AW 余単位の終域の比較。 -/
def unitComparison :
    _root_.SerrePositivity.NegativeTensor.extend (HomologicalComplex.tensorUnit (ModuleCat.{u} A) (.down ℕ)) ≅
      HomologicalComplex.tensorUnit (ModuleCat.{u} A) (.up ℤ) :=
  extendSingleIso ComplexShape.embeddingDownNat (𝟙_ (ModuleCat A)) 0 0 rfl

private lemma unitComparison_zero_apply :
    (_root_.SerrePositivity.NegativeTensor.unitComparison (A := A)).hom.f 0
      ((_root_.SerrePositivity.NegativeTensor.xIso (HomologicalComplex.tensorUnit (ModuleCat A) (.down ℕ)) 0).inv
        ((singleObjXSelf (.down ℕ) 0 (𝟙_ (ModuleCat A))).inv (1 : A))) =
      (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A) := by
  have he : (_root_.SerrePositivity.NegativeTensor.xIso (HomologicalComplex.tensorUnit (ModuleCat A) (.down ℕ)) 0).inv ≫
      (_root_.SerrePositivity.NegativeTensor.unitComparison (A := A)).hom.f 0 =
        (singleObjXSelf (.down ℕ) 0 (𝟙_ (ModuleCat A))).hom ≫
          (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv := by
    rw [_root_.SerrePositivity.NegativeTensor.unitComparison, extendSingleIso_hom_f]
    change (_root_.SerrePositivity.NegativeTensor.xIso (HomologicalComplex.tensorUnit (ModuleCat A) (.down ℕ)) 0).inv ≫
      (_root_.SerrePositivity.NegativeTensor.xIso (HomologicalComplex.tensorUnit (ModuleCat A) (.down ℕ)) 0).hom ≫ _ = _
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  have he' := congrArg (fun φ => (singleObjXSelf (.down ℕ) 0 (𝟙_ (ModuleCat A))).inv ≫ φ) he
  simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp] at he'
  exact congrArg (fun φ => φ (1 : A)) he'

private lemma natLeftUnitor_inv_apply (K : ChainComplex (ModuleCat.{u} A) ℕ)
    (n : ℕ) (x : K.X n) :
    (HomologicalComplex.leftUnitor K).inv.f n x =
      ιTensorObj (HomologicalComplex.tensorUnit (ModuleCat A) (.down ℕ)) K 0 n n (by omega)
        ((singleObjXSelf (.down ℕ) 0 (𝟙_ (ModuleCat A))).inv (1 : A) ⊗ₜ[A] x) := by
  change (HomologicalComplex.leftUnitor' K).inv n x = _
  rw [HomologicalComplex.leftUnitor'_inv]
  simp only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply]

private lemma cochainLeftUnitor_inv_apply (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (n : ℤ) (x : K.X n) :
    (HomologicalComplex.leftUnitor K).inv.f n x =
      ιTensorObj (HomologicalComplex.tensorUnit (ModuleCat A) (.up ℤ)) K 0 n n (by omega)
        ((singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A) ⊗ₜ[A] x) := by
  change (HomologicalComplex.leftUnitor' K).inv n x = _
  rw [HomologicalComplex.leftUnitor'_inv]
  simp only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.leftUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply]

/-- 概要：延長とテンソルの比較は左単位子を保つ（Berger–Fresse §1.1 の次数規約）。
方針：負次数で左単位子を零次と n 次の純テンソルとして計算する。
規約：単位の比較には single 複体の標準同型を使う。
使われ方：鎖 AW 対角の左余単位則を整数模型へ移す。 -/
lemma comparison_leftUnitor (K : ChainComplex (ModuleCat.{u} A) ℕ) :
    extendMap (HomologicalComplex.leftUnitor K).inv ComplexShape.embeddingDownNat ≫
        (_root_.SerrePositivity.NegativeTensor.comparison (HomologicalComplex.tensorUnit (ModuleCat A) (.down ℕ)) K).hom ≫
        HomologicalComplex.tensorHom (_root_.SerrePositivity.NegativeTensor.unitComparison (A := A)).hom (𝟙 (_root_.SerrePositivity.NegativeTensor.extend K)) =
      (HomologicalComplex.leftUnitor (_root_.SerrePositivity.NegativeTensor.extend K)).inv := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : 0 < i
  · exact (_root_.SerrePositivity.NegativeTensor.isZero_positive K i hi).eq_of_src _ _
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = -(n : ℤ) := ⟨(-i).toNat, by omega⟩
  apply (cancel_epi (_root_.SerrePositivity.NegativeTensor.xIso K n).inv).1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (HomologicalComplex.tensorHom (_root_.SerrePositivity.NegativeTensor.unitComparison (A := A)).hom (𝟙 (_root_.SerrePositivity.NegativeTensor.extend K))).f
      (-(n : ℤ))
      ((_root_.SerrePositivity.NegativeTensor.comparison (HomologicalComplex.tensorUnit (ModuleCat A) (.down ℕ)) K).hom.f (-(n : ℤ))
        ((extendMap (HomologicalComplex.leftUnitor K).inv ComplexShape.embeddingDownNat).f
          (-(n : ℤ)) ((_root_.SerrePositivity.NegativeTensor.xIso K n).inv x))) =
    (HomologicalComplex.leftUnitor (_root_.SerrePositivity.NegativeTensor.extend K)).inv.f (-(n : ℤ)) ((_root_.SerrePositivity.NegativeTensor.xIso K n).inv x)
  simp only [_root_.SerrePositivity.NegativeTensor.extendMap_neg_inv_apply, _root_.SerrePositivity.NegativeTensor.natLeftUnitor_inv_apply, _root_.SerrePositivity.NegativeTensor.comparison_neg_inv_apply,
    _root_.SerrePositivity.NegativeTensor.degreeMap_ι_tmul, SerrePositivity.cochainTensorMap_apply_ι,
    HomologicalComplex.id_f, ModuleCat.id_apply, _root_.SerrePositivity.NegativeTensor.cochainLeftUnitor_inv_apply]
  erw [_root_.SerrePositivity.NegativeTensor.unitComparison_zero_apply]
  rfl

private lemma natRightUnitor_inv_apply (K : ChainComplex (ModuleCat.{u} A) ℕ)
    (n : ℕ) (x : K.X n) :
    (HomologicalComplex.rightUnitor K).inv.f n x =
      ιTensorObj K (HomologicalComplex.tensorUnit (ModuleCat A) (.down ℕ)) n 0 n (by omega)
        (x ⊗ₜ[A] (singleObjXSelf (.down ℕ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) := by
  change (HomologicalComplex.rightUnitor' K).inv n x = _
  rw [HomologicalComplex.rightUnitor'_inv]
  simp only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply]

private lemma cochainRightUnitor_inv_apply (K : CochainComplex (ModuleCat.{u} A) ℤ)
    (n : ℤ) (x : K.X n) :
    (HomologicalComplex.rightUnitor K).inv.f n x =
      ιTensorObj K (HomologicalComplex.tensorUnit (ModuleCat A) (.up ℤ)) n 0 n (by omega)
        (x ⊗ₜ[A] (singleObjXSelf (.up ℤ) 0 (𝟙_ (ModuleCat A))).inv (1 : A)) := by
  change (HomologicalComplex.rightUnitor' K).inv n x = _
  rw [HomologicalComplex.rightUnitor'_inv]
  simp only [ModuleCat.comp_apply, ModuleCat.MonoidalCategory.rightUnitor_inv_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply]

/-- 概要：延長とテンソルの比較は右単位子を保つ（Berger–Fresse §1.1 の次数規約）。
方針：負次数で右単位子を零次と n 次の純テンソルとして計算する。
規約：単位の比較には single 複体の標準同型を使う。
使われ方：鎖 AW 対角の右余単位則を整数模型へ移す。 -/
lemma comparison_rightUnitor (K : ChainComplex (ModuleCat.{u} A) ℕ) :
    extendMap (HomologicalComplex.rightUnitor K).inv ComplexShape.embeddingDownNat ≫
        (_root_.SerrePositivity.NegativeTensor.comparison K (HomologicalComplex.tensorUnit (ModuleCat A) (.down ℕ))).hom ≫
        HomologicalComplex.tensorHom (𝟙 (_root_.SerrePositivity.NegativeTensor.extend K)) (_root_.SerrePositivity.NegativeTensor.unitComparison (A := A)).hom =
      (HomologicalComplex.rightUnitor (_root_.SerrePositivity.NegativeTensor.extend K)).inv := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : 0 < i
  · exact (_root_.SerrePositivity.NegativeTensor.isZero_positive K i hi).eq_of_src _ _
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = -(n : ℤ) := ⟨(-i).toNat, by omega⟩
  apply (cancel_epi (_root_.SerrePositivity.NegativeTensor.xIso K n).inv).1
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change (HomologicalComplex.tensorHom (𝟙 (_root_.SerrePositivity.NegativeTensor.extend K)) (_root_.SerrePositivity.NegativeTensor.unitComparison (A := A)).hom).f
      (-(n : ℤ))
      ((_root_.SerrePositivity.NegativeTensor.comparison K (HomologicalComplex.tensorUnit (ModuleCat A) (.down ℕ))).hom.f (-(n : ℤ))
        ((extendMap (HomologicalComplex.rightUnitor K).inv ComplexShape.embeddingDownNat).f
          (-(n : ℤ)) ((_root_.SerrePositivity.NegativeTensor.xIso K n).inv x))) =
    (HomologicalComplex.rightUnitor (_root_.SerrePositivity.NegativeTensor.extend K)).inv.f (-(n : ℤ)) ((_root_.SerrePositivity.NegativeTensor.xIso K n).inv x)
  simp only [_root_.SerrePositivity.NegativeTensor.extendMap_neg_inv_apply, _root_.SerrePositivity.NegativeTensor.natRightUnitor_inv_apply, _root_.SerrePositivity.NegativeTensor.comparison_neg_inv_apply,
    _root_.SerrePositivity.NegativeTensor.degreeMap_ι_tmul, SerrePositivity.cochainTensorMap_apply_ι,
    HomologicalComplex.id_f, ModuleCat.id_apply, _root_.SerrePositivity.NegativeTensor.cochainRightUnitor_inv_apply]
  erw [_root_.SerrePositivity.NegativeTensor.unitComparison_zero_apply]
  rfl

end SerrePositivity.NegativeTensor
