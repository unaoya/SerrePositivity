module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamily
public import Mathlib.Algebra.BigOperators.Fin

/-!
模型。文献の定義との比較は後で
# テンソル冪の有限族の連結

概要：Berger–Moerdijk §1 の Schur 合成に現れる入力のテンソル冪を連結する。
方針：有限族の先頭から、既存の反復テンソルの連結同型を適用する。
規約：空の族と零乗を含み、交換を使わず入力の順序を保つ。
使われ方：全入力へのオペラッド合成を自由代数の生成射上で適用する。
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

/-- 概要：テンソル冪の有限族を合計乗数のテンソル冪へ連結する同型（Berger–Moerdijk §1）。
方針：先頭因子と残りの族に分け、反復テンソルの連結同型を使う。
規約：入力の順序を保存し、零乗の因子も許す。
使われ方：自由代数の演算の入力を合計 arity で扱う。 -/
def tensorPowerFamilyIso (K : Complex A) : ∀ (n : ℕ) (s : Fin n → ℕ),
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => power K (s i)) ≅ power K (∑ i, s i)
  | 0, s => eqToIso (congrArg (power K) (Fin.sum_univ_zero s).symm)
  | n + 1, s =>
    whiskerLeftIso (power K (s 0)) (tensorPowerFamilyIso K n (fun i => s i.succ)) ≪≫
      appendIso K (s 0) (∑ i : Fin n, s i.succ) ≪≫
      eqToIso (congrArg (power K) (Fin.sum_univ_succ s).symm)

/-- 概要：テンソル冪の連結同型は底の複体射に関して自然（Berger–Moerdijk §1）。
方針：有限族の長さに関する帰納法と既存の連結同型の自然性を使う。
規約：各因子に同じ chain map のテンソル冪を適用する。
使われ方：自由代数の作用と底の複体射の両立を示す。 -/
lemma tensorPowerFamilyIso_naturality {K L : Complex A} (f : K ⟶ L)
    (n : ℕ) (s : Fin n → ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => _root_.SerrePositivity.TensorPowers.map f (s i)) ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso L n s).hom =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K n s).hom ≫ _root_.SerrePositivity.TensorPowers.map f (∑ i, s i) := by
  induction n with
  | zero =>
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso, Fin.sum_univ_zero, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap,
      _root_.SerrePositivity.TensorPowers.map, eqToIso.hom, eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
  | succ n ih =>
    dsimp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily]
    have ht :
        (_root_.SerrePositivity.TensorPowers.map f (s 0) ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => _root_.SerrePositivity.TensorPowers.map f (s i.succ))) ≫
          (power L (s 0) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso L n (fun i => s i.succ)).hom) =
        (power K (s 0) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K n (fun i => s i.succ)).hom) ≫
          (_root_.SerrePositivity.TensorPowers.map f (s 0) ⊗ₘ _root_.SerrePositivity.TensorPowers.map f (∑ i : Fin n, s i.succ)) := by
      simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.comp_id, Category.id_comp]
      rw [ih]
    change (_root_.SerrePositivity.TensorPowers.map f (s 0) ⊗ₘ
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyMap n (fun i => _root_.SerrePositivity.TensorPowers.map f (s i.succ))) ≫ _ = _
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso, Iso.trans_hom, whiskerLeftIso_hom, eqToIso.hom,
      Category.assoc]
    rw [← Category.assoc _ _ ((appendIso L (s 0) (∑ i : Fin n, s i.succ)).hom ≫ _), ht]
    simp only [Category.assoc]
    rw [← Category.assoc _ (appendIso L (s 0) (∑ i : Fin n, s i.succ)).hom,
      appendIso_naturality]
    simp only [Category.assoc]
    rw [_root_.SerrePositivity.TensorPowers.map_index_eq f (Fin.sum_univ_succ s).symm]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
