module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSeparationBraiding
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyUnit

/-!
模型。文献の定義との比較は後で
# 係数と入力の分離と末尾一因子の分離

概要：Berger–Moerdijk §1 の全合成で、末尾の演算の係数と入力を分離する。
方針：有限族の長さで帰納し、tensorμ の結合則と単位則を適用する。
規約：係数列と入力列の両方で元の順序を保つ。
使われ方：任意の二ブロックへの分離と係数・入力の分離を比較する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

set_option maxHeartbeats 800000 in
-- 先頭と尾に現れる複体のテンソル構造の定義的等しさの検査に通常より多くの探索を要する。
/-- 概要：係数と入力を分離する同型は末尾一因子の分離と両立する（Berger–Moerdijk §1）。
方針：先頭で再帰を展開し、尾への帰納仮定と tensorμ の結合則を適用する。
規約：前半の有限族の末尾に含まれる単位因子も保持する。
使われ方：入力族を二ブロックへ分ける計算の帰納段階に用いる。 -/
lemma tensorFamilyTensorIso_splitLast (n : ℕ) (V W : Fin (n + 1) → Complex A) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n (fun j => V j ⊗ W j)).hom ≫
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso n (fun j => V j.castSucc) (fun j => W j.castSucc)).hom ▷
        (V (Fin.last n) ⊗ W (Fin.last n))) ≫
      tensorμ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => V j.castSucc))
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => W j.castSucc)) (V (Fin.last n)) (W (Fin.last n)) =
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso (n + 1) V W).hom ≫
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n V).hom ⊗ₘ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n W).hom) := by
  induction n with
  | zero =>
    apply (cancel_mono ((λ_ (V (Fin.last 0))).hom ⊗ₘ
      (λ_ (W (Fin.last 0))).hom)).1
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast, Iso.trans_hom, Iso.symm_hom,
      Category.assoc, tensorHom_comp_tensorHom]
    erw [Iso.inv_hom_id, Iso.inv_hom_id]
    simp only [Category.comp_id]
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso_one]
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso, Iso.symm_hom]
    erw [← tensor_left_unitality]
    erw [Iso.inv_hom_id]
    simp only [Category.comp_id]
  | succ n ih =>
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso]
    simp only [Iso.trans_hom, whiskerLeftIso_hom, Iso.symm_hom, Category.assoc]
    simp only [comp_whiskerRight, Category.assoc]
    erw [← associator_inv_naturality_middle_assoc]
    erw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorμ_associativity_inv]
    erw [← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc]
    simp only [Category.assoc]
    erw [ih (fun j => V j.succ) (fun j => W j.succ)]
    simp only [whiskerLeft_comp, Category.assoc]
    erw [tensorμ_natural_right_assoc]
    conv_rhs =>
      arg 1
      change ((V 0 ⊗ W 0) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso (n + 1)
        (fun j => V j.succ) (fun j => W j.succ)).hom) ≫
        tensorμ (V 0) (W 0) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 1) (fun j => V j.succ))
          (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 1) (fun j => W j.succ))
    conv_rhs => rw [Category.assoc]
    conv_rhs =>
      arg 2
      arg 2
      arg 1
      change (V 0 ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n (fun j => V j.succ)).hom) ≫
        (α_ (V 0) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => V j.castSucc.succ)) (V (Fin.last (n + 1)))).inv
    conv_rhs =>
      arg 2
      arg 2
      arg 2
      change (W 0 ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n (fun j => W j.succ)).hom) ≫
        (α_ (W 0) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => W j.castSucc.succ)) (W (Fin.last (n + 1)))).inv
    erw [tensorHom_comp_tensorHom]
    rfl

/-- 概要：末尾の再結合の後の分離は、前半と末尾を独立に分離して再結合する式となる（Berger–Moerdijk §1）。
方針：末尾分離との両立に始域と終域の逆射を合成して相殺する。
規約：出力の係数列と入力列のそれぞれで末尾を再結合する。
使われ方：二ブロック分離で後半の最後の因子を再結合する計算に用いる。 -/
lemma tensorFamilyTensorIso_splitLast_inv (n : ℕ) (V W : Fin (n + 1) → Complex A) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n (fun j => V j ⊗ W j)).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso (n + 1) V W).hom =
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso n (fun j => V j.castSucc) (fun j => W j.castSucc)).hom ▷
      (V (Fin.last n) ⊗ W (Fin.last n))) ≫
      tensorμ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => V j.castSucc))
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => W j.castSucc)) (V (Fin.last n)) (W (Fin.last n)) ≫
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n V).inv ⊗ₘ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n W).inv) := by
  have h := congrArg (fun z => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n (fun j => V j ⊗ W j)).inv ≫ z ≫
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n V).inv ⊗ₘ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n W).inv))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso_splitLast n V W)
  simpa only [Category.assoc, Iso.inv_hom_id_assoc, tensorHom_comp_tensorHom,
    Iso.hom_inv_id, tensorHom_id, id_whiskerRight, Category.comp_id] using h.symm

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
