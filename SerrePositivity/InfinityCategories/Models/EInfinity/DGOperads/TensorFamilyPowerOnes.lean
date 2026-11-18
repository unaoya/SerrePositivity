module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyGeneratorMap
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyPowerSplitAt

/-!
模型。文献の定義との比較は後で
# 一次のテンソル冪の有限族の連結

概要：Berger–Moerdijk §1 の入力の連結を、全ブロックの長さが一の場合に計算する。
方針：先頭で帰納し、一次の連結の式と右単位子を使う。
規約：一次のテンソル冪には右側の単位因子を含める。
使われ方：有限族から移したテンソル冪の分離と標準の連結同型を比較する。
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

/-- 概要：一次のテンソル冪の連結は各単位因子を除く有限生成射に一致する（Berger–Moerdijk §1）。
方針：先頭の再帰で一次の連結を右単位子へ簡約し、残りへ帰納仮定を使う。
規約：有限和の総 arity を入力数 n へ移送する。
使われ方：標準の連結同型と有限族の分離から得られる同型を比較する。 -/
lemma tensorPowerFamilyIso_ones (X : Complex A) (n : ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso X n (fun _ => 1)).hom ≫
      eqToHom (congrArg (power X) (by simp : (∑ _ : Fin n, 1) = n)) =
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator X (fun _ : ℕ => power X 1) (fun _ => (ρ_ X).hom) n (fun _ => 1) := by
  induction n with
  | zero =>
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyGenerator, eqToIso.hom, eqToHom_trans]
    rfl
  | succ n ih =>
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso]
    simp only [Iso.trans_hom, whiskerLeftIso_hom, eqToIso.hom, Category.assoc,
      eqToHom_trans]
    rw [appendIso_one_left]
    simp only [Category.assoc, eqToHom_trans]
    erw [whisker_exchange_assoc]
    rw [power_index_succ X (by simp : (∑ _ : Fin n, 1) = n)]
    rw [← whiskerLeft_comp, ih, ← tensorHom_def]
    rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
