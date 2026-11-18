module

public import SerrePositivity.HomologicalAlgebra.Complexes.NegativeTensor.Naturality
public import SerrePositivity.HomologicalAlgebra.CochainTensor.Shuffle

/-!
# 負次数テンソル比較と結合子

概要：Berger–Fresse §1.1 の次数変更のテンソル比較が結合子を保つことを証明する。
方針：自然数の三次数の純テンソルで検査し、標準比較の成分公式を計算する。
規約：自然数鎖・整数コチェインの既存の結合子を用いる。
使われ方：AW の余結合性を整数コチェイン模型へ移す。
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

/-- 概要：標準同型で戻した元への延長射の値（Berger–Fresse §1.1）。
方針：次数同型の自然性を元に評価する。
規約：元の自然数鎖の任意の元を扱う。
使われ方：三重テンソル上で比較の可換性を計算する。 -/
@[simp] lemma extendMap_neg_inv_apply {K L : ChainComplex (ModuleCat.{u} A) ℕ}
    (f : K ⟶ L) (n : ℕ) (x : K.X n) :
    (extendMap f ComplexShape.embeddingDownNat).f (-(n : ℤ)) ((_root_.SerrePositivity.NegativeTensor.xIso K n).inv x) =
      (_root_.SerrePositivity.NegativeTensor.xIso L n).inv (f.f n x) :=
  congrArg (fun φ => φ x) (_root_.SerrePositivity.NegativeTensor.xIso_inv_extendMap f n)

/-- 概要：比較写像の標準同型から来る元での値（Berger–Fresse §1.1）。
方針：次数成分の公式で同型と逆同型を消す。
規約：元は自然数テンソルの全次数に属する。
使われ方：比較と結合子の適合性を元で検証する。 -/
@[simp] lemma comparison_neg_inv_apply (K L : ChainComplex (ModuleCat.{u} A) ℕ)
    (n : ℕ) (x : (HomologicalComplex.tensorObj K L).X n) :
    (_root_.SerrePositivity.NegativeTensor.comparison K L).hom.f (-(n : ℤ))
        ((_root_.SerrePositivity.NegativeTensor.xIso (HomologicalComplex.tensorObj K L) n).inv x) = _root_.SerrePositivity.NegativeTensor.degreeMap K L n x := by
  have he : (_root_.SerrePositivity.NegativeTensor.xIso (HomologicalComplex.tensorObj K L) n).inv ≫
      (_root_.SerrePositivity.NegativeTensor.comparison K L).hom.f (-(n : ℤ)) = _root_.SerrePositivity.NegativeTensor.degreeMap K L n := by
    rw [_root_.SerrePositivity.NegativeTensor.comparison_hom_f_neg]
    simp only [← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  exact congrArg (fun φ => φ x) he

/-- 概要：テンソル次数比較の斉次純テンソルでの値（Berger–Fresse §1.1）。
方針：直和包含との合成公式を純テンソルで評価する。
規約：二次数 p,q の和は n。
使われ方：比較と結合子の適合性を元で検証する。 -/
@[simp] lemma degreeMap_ι_tmul (K L : ChainComplex (ModuleCat.{u} A) ℕ)
    (n p q : ℕ) (h : p + q = n) (x : K.X p) (y : L.X q) :
    _root_.SerrePositivity.NegativeTensor.degreeMap K L n (ιTensorObj K L p q n h (x ⊗ₜ[A] y)) =
      ιTensorObj (_root_.SerrePositivity.NegativeTensor.extend K) (_root_.SerrePositivity.NegativeTensor.extend L) (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ)) (by omega)
        ((_root_.SerrePositivity.NegativeTensor.xIso K p).inv x ⊗ₜ[A] (_root_.SerrePositivity.NegativeTensor.xIso L q).inv y) := by
  have hv := congrArg (fun φ => φ (x ⊗ₜ[A] y)) (_root_.SerrePositivity.NegativeTensor.ι_degreeMap K L n p q h)
  change _root_.SerrePositivity.NegativeTensor.degreeMap K L n (ιTensorObj K L p q n h (x ⊗ₜ[A] y)) =
    ιTensorObj (_root_.SerrePositivity.NegativeTensor.extend K) (_root_.SerrePositivity.NegativeTensor.extend L) (-(p : ℤ)) (-(q : ℤ)) (-(n : ℤ)) _
      (((_root_.SerrePositivity.NegativeTensor.xIso K p).inv ⊗ₘ (_root_.SerrePositivity.NegativeTensor.xIso L q).inv) (x ⊗ₜ[A] y)) at hv
  simpa only [ModuleCat.MonoidalCategory.tensorHom_tmul] using hv

private lemma natAssociator_ι_tmul (K L M : ChainComplex (ModuleCat.{u} A) ℕ)
    (p q r n : ℕ) (h : p + q + r = n) (x : K.X p) (y : L.X q) (z : M.X r) :
    (HomologicalComplex.associator K L M).hom.f n
      (ιTensorObj (HomologicalComplex.tensorObj K L) M (p + q) r n h
        (ιTensorObj K L p q (p + q) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z)) =
      ιTensorObj K (HomologicalComplex.tensorObj L M) p (q + r) n (by omega)
        (x ⊗ₜ[A] ιTensorObj L M q r (q + r) rfl (y ⊗ₜ[A] z)) :=
  congrArg (fun φ => φ ((x ⊗ₜ[A] y) ⊗ₜ[A] z))
    (GradedObject.Monoidal.ιTensorObj₃'_associator_hom K.X L.X M.X p q r n h)

private lemma cochainAssociator_sums
    (K L M : CochainComplex (ModuleCat.{u} A) ℤ) (i j k s t n : ℤ)
    (hs : i + j = s) (ht : j + k = t) (hn : s + k = n)
    (x : K.X i) (y : L.X j) (z : M.X k) :
    (HomologicalComplex.associator K L M).hom.f n
      (ιTensorObj (HomologicalComplex.tensorObj K L) M s k n hn
        (ιTensorObj K L i j s hs (x ⊗ₜ[A] y) ⊗ₜ[A] z)) =
      ιTensorObj K (HomologicalComplex.tensorObj L M) i t n (by omega)
        (x ⊗ₜ[A] ιTensorObj L M j k t ht (y ⊗ₜ[A] z)) := by
  subst s
  subst t
  exact SerrePositivity.cochainTensorAssociator_hom_apply_ι K L M i j k n hn x y z

/-- 概要：延長とテンソルの比較は結合子を保つ（Berger–Fresse §1.1 の次数規約）。
方針：負の全次数を自然数の三重直和へ戻し、純テンソルで比較する。
規約：二つの結合順序で同じ三つの次数同型を使う。
使われ方：AW 鎖対角の余結合性を整数模型へ移す。 -/
lemma comparison_associator (K L M : ChainComplex (ModuleCat.{u} A) ℕ) :
    (_root_.SerrePositivity.NegativeTensor.comparison (HomologicalComplex.tensorObj K L) M).hom ≫
        HomologicalComplex.tensorHom (_root_.SerrePositivity.NegativeTensor.comparison K L).hom (𝟙 (_root_.SerrePositivity.NegativeTensor.extend M)) ≫
        (HomologicalComplex.associator (_root_.SerrePositivity.NegativeTensor.extend K) (_root_.SerrePositivity.NegativeTensor.extend L) (_root_.SerrePositivity.NegativeTensor.extend M)).hom =
      extendMap (HomologicalComplex.associator K L M).hom ComplexShape.embeddingDownNat ≫
        (_root_.SerrePositivity.NegativeTensor.comparison K (HomologicalComplex.tensorObj L M)).hom ≫
        HomologicalComplex.tensorHom (𝟙 (_root_.SerrePositivity.NegativeTensor.extend K)) (_root_.SerrePositivity.NegativeTensor.comparison L M).hom := by
  apply HomologicalComplex.hom_ext
  intro i
  by_cases hi : 0 < i
  · exact (_root_.SerrePositivity.NegativeTensor.isZero_positive (HomologicalComplex.tensorObj
      (HomologicalComplex.tensorObj K L) M) i hi).eq_of_src _ _
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, i = -(n : ℤ) := ⟨(-i).toNat, by omega⟩
  apply (cancel_epi (_root_.SerrePositivity.NegativeTensor.xIso (HomologicalComplex.tensorObj
    (HomologicalComplex.tensorObj K L) M) n).inv).1
  apply mapBifunctor₁₂.hom_ext
  intro p q r hpqr
  change p + q + r = n at hpqr
  apply ModuleCat.hom_ext
  apply TensorProduct.ext_threefold
  intro x y z
  let v := ιTensorObj (HomologicalComplex.tensorObj K L) M (p + q) r n hpqr
    (ιTensorObj K L p q (p + q) rfl (x ⊗ₜ[A] y) ⊗ₜ[A] z)
  change (HomologicalComplex.associator (_root_.SerrePositivity.NegativeTensor.extend K) (_root_.SerrePositivity.NegativeTensor.extend L) (_root_.SerrePositivity.NegativeTensor.extend M)).hom.f (-(n : ℤ))
      ((HomologicalComplex.tensorHom (_root_.SerrePositivity.NegativeTensor.comparison K L).hom (𝟙 (_root_.SerrePositivity.NegativeTensor.extend M))).f (-(n : ℤ))
        ((_root_.SerrePositivity.NegativeTensor.comparison (HomologicalComplex.tensorObj K L) M).hom.f (-(n : ℤ))
          ((_root_.SerrePositivity.NegativeTensor.xIso (HomologicalComplex.tensorObj (HomologicalComplex.tensorObj K L) M) n).inv v))) =
    (HomologicalComplex.tensorHom (𝟙 (_root_.SerrePositivity.NegativeTensor.extend K)) (_root_.SerrePositivity.NegativeTensor.comparison L M).hom).f (-(n : ℤ))
      ((_root_.SerrePositivity.NegativeTensor.comparison K (HomologicalComplex.tensorObj L M)).hom.f (-(n : ℤ))
        ((extendMap (HomologicalComplex.associator K L M).hom ComplexShape.embeddingDownNat).f
          (-(n : ℤ))
          ((_root_.SerrePositivity.NegativeTensor.xIso (HomologicalComplex.tensorObj (HomologicalComplex.tensorObj K L) M) n).inv v)))
  simp only [_root_.SerrePositivity.NegativeTensor.extendMap_neg_inv_apply, v, _root_.SerrePositivity.NegativeTensor.natAssociator_ι_tmul,
    _root_.SerrePositivity.NegativeTensor.comparison_neg_inv_apply, _root_.SerrePositivity.NegativeTensor.degreeMap_ι_tmul,
    SerrePositivity.cochainTensorMap_apply_ι, HomologicalComplex.id_f, ModuleCat.id_apply]
  exact _root_.SerrePositivity.NegativeTensor.cochainAssociator_sums (_root_.SerrePositivity.NegativeTensor.extend K) (_root_.SerrePositivity.NegativeTensor.extend L) (_root_.SerrePositivity.NegativeTensor.extend M)
    (-(p : ℤ)) (-(q : ℤ)) (-(r : ℤ)) (-((p + q : ℕ) : ℤ)) (-((q + r : ℕ) : ℤ)) (-(n : ℤ))
    (by omega) (by omega) (by omega) ((_root_.SerrePositivity.NegativeTensor.xIso K p).inv x) ((_root_.SerrePositivity.NegativeTensor.xIso L q).inv y) ((_root_.SerrePositivity.NegativeTensor.xIso M r).inv z)

end SerrePositivity.NegativeTensor
