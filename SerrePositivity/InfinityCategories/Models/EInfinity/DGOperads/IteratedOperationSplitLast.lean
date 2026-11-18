module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.IteratedOperationTensor
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyTensorSplitLast
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorTailSeparationNaturality

/-!
模型。文献の定義との比較は後で
# 反復合成のテンソル射の最後の演算の分離

概要：Berger–Moerdijk §1 の末尾入力付き反復合成を最後の演算に沿って分離する。
方針：有限テンソル対の最後の分離を、係数列と入力列の最後の分離へ移す。
規約：係数列と入力列の順序はそれぞれ保つ。
使われ方：係数側と入力側の再帰式を反復合成のテンソル射へ適用する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily _root_.SerrePositivity.TensorPowers.power
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：最後の演算対を分離した反復合成は係数と入力の二列の分離で計算できる（Berger–Moerdijk §1）。
方針：有限テンソル対の分離の比較式と、末尾を保つ分離の自然性を用いる。
規約：最後の係数 L と入力 Z を含む前半の係数列 V と入力列 W を別々に扱う。
使われ方：反復合成のテンソル射の再帰を係数と入力の再帰から証明する。 -/
lemma iteratedOperationTensor_splitLast (P : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad A) (K : Complex A)
    (n k : ℕ) (s : Fin (n + 1) → ℕ) :
    let R := P.arity (n + 1 + k)
    let V := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => P.arity (s j.castSucc))
    let W := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => power K (s j.castSucc))
    let L := P.arity (s (Fin.last n))
    let Z := power K (s (Fin.last n))
    let T := power K k
    (R ◁ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n (fun j => P.arity (s j) ⊗ power K (s j))).inv ▷ T)) ≫
      P.iteratedOperationTensor K (n + 1) k s =
    (R ◁ (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso n (fun j => P.arity (s j.castSucc))
      (fun j => power K (s j.castSucc))).hom ▷ (L ⊗ Z)) ▷ T)) ≫
      (R ◁ (tensorμ V W L Z ▷ T)) ≫
      (R ◁ (α_ (V ⊗ L) (W ⊗ Z) T).hom) ≫ (α_ R (V ⊗ L) ((W ⊗ Z) ⊗ T)).inv ≫
      (((R ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n (fun j => P.arity (s j))).inv) ≫
        P.composeFirstInputs (n + 1) k s) ⊗ₘ
      (((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n (fun j => power K (s j))).inv ▷ T) ≫
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K (n + 1) s).hom ▷ T) ≫
        (appendIso K (∑ j, s j) k).hom)) := by
  dsimp only
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad.iteratedOperationTensor
  rw [← whiskerLeft_comp_assoc, ← comp_whiskerRight, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso_splitLast_inv]
  simp only [comp_whiskerRight, whiskerLeft_comp, Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorTailSeparation_naturality]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.Operad
