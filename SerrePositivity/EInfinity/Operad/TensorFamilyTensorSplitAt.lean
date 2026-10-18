module

public import SerrePositivity.EInfinity.Operad.TensorFamilyTensorSplitLast
public import SerrePositivity.EInfinity.Operad.TensorFamilySplitAt

/-!
# 係数と入力の分離と二ブロックへの分離

概要：Berger–Moerdijk §1 の自由代数の合成で、入力族の二ブロック分離を係数列と入力列へ移す。
方針：後半の長さで帰納し、末尾分離との両立と tensorμ の結合則を使う。
規約：前半と後半の順序を保ち、空の族も含める。
使われ方：部分合成後の全合成と二段の全合成の生成射を比較する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] tensorFamily
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

set_option maxHeartbeats 800000 in
-- 複体のテンソル構造と有限族の添字の定義的等しさを比較するため探索上限を局所的に増やす。
/-- 概要：係数と入力の分離は任意の二ブロックへの分離と両立する（Berger–Moerdijk §1）。
方針：後半の末尾を分離して帰納仮定を適用し、tensorμ の結合則で二列を再構成する。
規約：各列の前半と後半のテンソル積を終域に置く。
使われ方：自由代数の部分合成則の係数側と入力側の計算を同時に分離する。 -/
lemma tensorFamilyTensorIso_splitAt (n m : ℕ) (V W : Fin (n + m) → Complex A) :
    (tensorFamilySplitAt n m (fun j => V j ⊗ W j)).hom ≫
      ((tensorFamilyTensorIso n (fun j => V (j.castAdd m)) (fun j => W (j.castAdd m))).hom ⊗ₘ
        (tensorFamilyTensorIso m (fun j => V (j.natAdd n)) (fun j => W (j.natAdd n))).hom) ≫
      tensorμ (tensorFamily n (fun j => V (j.castAdd m)))
        (tensorFamily n (fun j => W (j.castAdd m)))
        (tensorFamily m (fun j => V (j.natAdd n)))
        (tensorFamily m (fun j => W (j.natAdd n))) =
    (tensorFamilyTensorIso (n + m) V W).hom ≫
      ((tensorFamilySplitAt n m V).hom ⊗ₘ (tensorFamilySplitAt n m W).hom) := by
  induction m with
  | zero =>
    apply (cancel_mono ((ρ_ (tensorFamily n (fun j => V (j.castAdd 0)))).hom ⊗ₘ
      (ρ_ (tensorFamily n (fun j => W (j.castAdd 0)))).hom)).1
    simp only [tensorFamilySplitAt, Iso.symm_hom, Category.assoc,
      tensorHom_comp_tensorHom, Iso.inv_hom_id, tensorHom_id,
      id_whiskerRight, Category.comp_id]
    erw [rightUnitor_inv_comp_tensorHom_assoc]
    rw [tensorFamilyTensorIso]
    simp only [Iso.symm_hom]
    erw [← tensor_right_unitality]
    erw [Iso.inv_hom_id]
    simp only [Category.comp_id]
    rfl
  | succ m ih =>
    simp only [tensorFamilySplitAt, Iso.trans_hom, whiskerRightIso_hom,
      whiskerLeftIso_hom, Iso.symm_hom, Category.assoc]
    rw [whiskerLeft_comp_tensorHom_assoc]
    erw [tensorFamilyTensorIso_splitLast_inv m
      (fun j => V (j.natAdd n)) (fun j => W (j.natAdd n))]
    rw [← tensorHom_comp_whiskerLeft]
    simp only [whiskerLeft_comp, Category.assoc]
    erw [tensorμ_natural_right]
    conv_lhs =>
      arg 2
      arg 2
      arg 2
      arg 1
      arg 2
      rw [← tensorHom_id]
    erw [← associator_naturality_assoc]
    erw [← tensor_associativity_assoc]
    erw [tensorHom_id]
    erw [← comp_whiskerRight_assoc, ← comp_whiskerRight_assoc]
    simp only [Category.assoc]
    erw [ih (fun j => V j.castSucc) (fun j => W j.castSucc)]
    simp only [comp_whiskerRight, Category.assoc]
    erw [tensorμ_natural_left_assoc]
    erw [reassoc_of% (tensorFamilyTensorIso_splitLast (n + m) V W)]
    simp only [tensorHom_comp_tensorHom]
    rfl

/-- 概要：二ブロックを再結合した後の係数・入力の分離を二列の再結合で計算できる（Berger–Moerdijk §1）。
方針：二ブロック分離との両立に分離同型の逆射を前後から合成して相殺する。
規約：係数列と入力列でそれぞれ前半と後半を再結合する。
使われ方：内側の演算を合成した生成射を外側の入力族へ組み込む。 -/
lemma tensorFamilyTensorIso_splitAt_inv (n m : ℕ) (V W : Fin (n + m) → Complex A) :
    (tensorFamilySplitAt n m (fun j => V j ⊗ W j)).inv ≫
      (tensorFamilyTensorIso (n + m) V W).hom =
    ((tensorFamilyTensorIso n (fun j => V (j.castAdd m)) (fun j => W (j.castAdd m))).hom ⊗ₘ
      (tensorFamilyTensorIso m (fun j => V (j.natAdd n)) (fun j => W (j.natAdd n))).hom) ≫
      tensorμ (tensorFamily n (fun j => V (j.castAdd m)))
        (tensorFamily n (fun j => W (j.castAdd m)))
        (tensorFamily m (fun j => V (j.natAdd n)))
        (tensorFamily m (fun j => W (j.natAdd n))) ≫
      ((tensorFamilySplitAt n m V).inv ⊗ₘ (tensorFamilySplitAt n m W).inv) := by
  have h := congrArg (fun z => (tensorFamilySplitAt n m (fun j => V j ⊗ W j)).inv ≫ z ≫
    ((tensorFamilySplitAt n m V).inv ⊗ₘ (tensorFamilySplitAt n m W).inv))
    (tensorFamilyTensorIso_splitAt n m V W)
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, tensorHom_comp_tensorHom,
    Iso.hom_inv_id, tensorHom_id, id_whiskerRight, Category.comp_id] using h.symm

end SerrePositivity.EInfinity
