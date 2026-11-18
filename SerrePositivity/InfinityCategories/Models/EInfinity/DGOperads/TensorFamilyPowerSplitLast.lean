module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyPowerTail
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyUnit

/-!
模型。文献の定義との比較は後で
# テンソル冪の連結と末尾一因子の分離

概要：Berger–Moerdijk §1 の全合成の入力側で、末尾の演算の入力を分離する。
方針：族の長さで帰納し、テンソル冪の連結の結合則と単位則を使う。
規約：連結は入力の順序を保ち、末尾の arity が零の場合も含む。
使われ方：入力族の二ブロック分離と連結の両立を帰納的に証明する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.TensorPowers
open scoped _root_.BigOperators

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：有限族の連結は末尾を分離してからの連結に等しい（Berger–Moerdijk §1）。
方針：先頭での再帰を使い、尾への帰納仮定を連結の結合則で持ち上げる。
規約：出力の長さを前半の和と末尾の arity の和で表す。
使われ方：全合成の入力側を末尾から計算する。 -/
lemma tensorPowerFamilyIso_splitLast (K : Complex A) (n : ℕ) (s : Fin (n + 1) → ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K (n + 1) s).hom ≫
      eqToHom (congrArg (power K) (Fin.sum_univ_castSucc s)) =
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n (fun j => power K (s j))).hom ≫
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K n (fun j => s j.castSucc)).hom ⊗ₘ
        𝟙 (power K (s (Fin.last n)))) ≫
      (appendIso K (∑ j : Fin n, s j.castSucc) (s (Fin.last n))).hom := by
  induction n with
  | zero =>
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso_one]
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso]
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast, Iso.trans_hom, Iso.symm_hom, eqToIso.hom,
      tensorHom_id, Category.assoc]
    erw [appendIso_index_left K (Fin.sum_univ_zero (fun j : Fin 0 => s j.castSucc)).symm]
    rw [appendIso_zero_left]
    simp only [Category.assoc, eqToHom_trans]
    erw [Iso.inv_hom_id_assoc]
  | succ n ih =>
    apply (cancel_mono (eqToHom (congrArg (power K)
      ((congrArg (· + s (Fin.last (n + 1)))
        (Fin.sum_univ_succ (fun j : Fin (n + 1) => s j.castSucc))).trans
        (Nat.add_assoc (s 0) (∑ j : Fin n, s j.succ.castSucc)
          (s (Fin.last (n + 1)))))))).1
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast]
    simp only [Iso.trans_hom,
      whiskerLeftIso_hom, Iso.symm_hom, eqToIso.hom, tensorHom_id,
      Category.assoc]
    conv_rhs =>
      arg 2
      arg 2
      arg 1
      arg 1
      rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso]
    simp only [Iso.trans_hom, whiskerLeftIso_hom, eqToIso.hom,
      comp_whiskerRight, Category.assoc]
    rw [appendIso_index_left_assoc K
      (Fin.sum_univ_succ (fun j : Fin (n + 1) => s j.castSucc)).symm]
    simp only [eqToHom_trans]
    erw [appendIso_associativity]
    erw [← associator_inv_naturality_middle_assoc]
    erw [Iso.inv_hom_id_assoc]
    erw [← whiskerLeft_comp_assoc, ← whiskerLeft_comp_assoc]
    have hi := ih (fun j => s j.succ)
    simp only [tensorHom_id] at hi
    simp only [Category.assoc]
    erw [← hi]
    rw [whiskerLeft_comp_assoc]
    erw [appendIso_index_right K (s 0) (Fin.sum_univ_castSucc (fun j => s j.succ))]
/-- 概要：末尾を再結合した後の連結は前半と末尾のテンソル冪の連結となる（Berger–Moerdijk §1）。
方針：末尾分離との両立に逆の分離射を前置し、総 arity の移送を戻す。
規約：終域を元の族の arity の和で表す。
使われ方：二ブロックへの分離で後半の再結合と連結を相殺する。 -/
lemma tensorPowerFamilyIso_splitLast_inv (K : Complex A) (n : ℕ) (s : Fin (n + 1) → ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n (fun j => power K (s j))).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K (n + 1) s).hom =
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K n (fun j => s j.castSucc)).hom ⊗ₘ
      𝟙 (power K (s (Fin.last n)))) ≫
      (appendIso K (∑ j : Fin n, s j.castSucc) (s (Fin.last n))).hom ≫
      eqToHom (congrArg (power K) (Fin.sum_univ_castSucc s).symm) := by
  have h := congrArg (fun z =>
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n (fun j => power K (s j))).inv ≫ z ≫
      eqToHom (congrArg (power K) (Fin.sum_univ_castSucc s).symm))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso_splitLast K n s)
  simpa only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id,
    Iso.inv_hom_id_assoc] using h

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
