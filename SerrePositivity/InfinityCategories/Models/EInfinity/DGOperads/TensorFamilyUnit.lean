module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SchurComposition
public import SerrePositivity.CategoryTheory.Monoidal.TensorPower.Basic

/-!
模型。文献の定義との比較は後で
# 一要素の有限テンソル族の比較同型と単位子

概要：Berger–Moerdijk §1 の自由代数の単位作用で、一次の入力族に付くテンソル単位を除く。
方針：係数と入力の分離の単位則と、テンソル冪の連結の零乗の計算則を使う。
規約：有限テンソルは右括弧とし、最後のテンソル単位を含む。
使われ方：Schur 演算の一次の場合を通常の Schur 生成射へ簡約する。
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

/-- 概要：一次の係数と入力の分離は右単位子と両立する（Berger–Moerdijk §1）。
方針：テンソル関手の右単位則を適用する。
規約：二つの入力族は一要素。
使われ方：自由代数の一次の演算で余分なテンソル単位を除く。 -/
lemma tensorFamilyTensorIso_one (V W : Fin 1 → Complex A) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso 1 V W).hom ≫ ((ρ_ (V 0)).hom ⊗ₘ (ρ_ (W 0)).hom) =
      (ρ_ (V 0 ⊗ W 0)).hom := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily, Iso.trans_hom, whiskerLeftIso_hom,
    Iso.symm_hom, Category.assoc]
  exact (tensor_right_unitality (V 0) (W 0)).symm

/-- 概要：一次の入力のテンソル冪の連結は右単位子と arity の移送である（Berger–Moerdijk §1）。
方針：空の残りの族の総和を 0 とし、零乗を連結する同型を簡約する。
規約：一要素の arity 族の総和への等式の射を末尾に置く。
使われ方：自由代数の単位作用の生成射上の入力の式を簡約する。 -/
lemma tensorPowerFamilyIso_one (K : Complex A) (s : Fin 1 → ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K 1 s).hom = (ρ_ (power K (s 0))).hom ≫
      eqToHom (congrArg (power K) (by simp : s 0 = ∑ i, s i)) := by
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily, Fin.sum_univ_zero, Iso.trans_hom,
    whiskerLeftIso_hom, eqToIso.hom, eqToHom_refl, whiskerLeft_id, Category.id_comp]
  rw [appendIso_zero_right]
  simp only [Category.comp_id]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
