module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.FirstBlockFamilyAssembly
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyPowerHeadAssembly

/-!
模型。文献の定義との比較は後で
# 先頭ブロックの入力をまとめる連結の結合則

概要：Berger–Moerdijk §1 の二段の全合成で入力テンソル冪の連結を比較する。
方針：先頭ブロックの入力を連結してから外側へ組み込む計算を、二ブロックの連結へ移す。
規約：最終的な入力の arity は元の有限族の和とする。
使われ方：Schur 作用の部分合成則の入力側の結合則となる。
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

/-- 概要：先頭の入力 arity を移送した組み込みは先頭と後半の連結に一致する（Berger–Moerdijk §1）。
方針：arity の表示の等式を消去し、先頭を組み込んだ連結の式を適用する。
規約：総 arity の等式 e で終域を元の族の和へ移送する。
使われ方：先頭ブロックの総入力数で表した連結を計算する。 -/
lemma arityHeadAssembly_power (K : Complex A) (m : ℕ) (s : Fin (1 + m) → ℕ)
    (q : ℕ) (t : Fin m → ℕ) (hq : q = s ((0 : Fin 1).castAdd m))
    (ht : t = fun j => s (j.natAdd 1)) (e : q + (∑ j, t j) = ∑ j, s j) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.arityHeadAssembly (power K) m s q t hq ht ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K (1 + m) s).hom =
      (power K q ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K m t).hom) ≫
        (appendIso K q (∑ j, t j)).hom ≫ eqToHom (congrArg (power K) e) := by
  subst q
  subst t
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.arityHeadAssembly, eqToHom_refl, Category.id_comp] using
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso_headAssembly K m s

/-- 概要：先頭ブロックの入力を組み込んだ後の連結は前半と後半の連結で計算できる（Berger–Moerdijk §1）。
方針：先頭ブロックの arity 族に移送した先頭の連結式を適用する。
規約：最後に元の入力族の総 arity へ戻す。
使われ方：内側で連結した入力を外側の全合成に渡す。 -/
lemma firstBlockFamilyAssembly_power (K : Complex A) (n m : ℕ) (s : Fin (n + m) → ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockFamilyAssembly (power K) n m s ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K (1 + m) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities n m s)).hom ≫
      eqToHom (congrArg (power K) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities_sum n m s)) =
    (power K (∑ j : Fin n, s (j.castAdd m)) ◁
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K m (fun j => s (j.natAdd n))).hom) ≫
      (appendIso K (∑ j : Fin n, s (j.castAdd m)) (∑ j : Fin m, s (j.natAdd n))).hom ≫
      eqToHom (congrArg (power K) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_sum_splitAt n m s).symm) := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.arityHeadAssembly_power K m (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities n m s)
    (∑ j : Fin n, s (j.castAdd m)) (fun j => s (j.natAdd n))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities_head n m s).symm
    (funext fun j => (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities_tail n m s j).symm)
    (by rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities_sum]; exact (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_sum_splitAt n m s).symm)
  have h' := congrArg (· ≫ eqToHom (congrArg (power K) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities_sum n m s))) h
  simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockFamilyAssembly, Category.assoc, eqToHom_trans] using h'

/-- 概要：先頭ブロックを先に連結してから外側で連結すると全入力の連結に等しい（Berger–Moerdijk §1）。
方針：まとめた先頭の組み込みの式を二ブロックの連結の両立へ接続する。
規約：空の前半と後半および零 arity の因子も含む。
使われ方：二段の Schur 演算の入力側の結合を処理する。 -/
lemma tensorPowerFamilyIso_firstBlock (K : Complex A) (n m : ℕ) (s : Fin (n + m) → ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt n m (fun j => power K (s j))).hom ≫
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K n (fun j => s (j.castAdd m))).hom ▷
        _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => power K (s (j.natAdd n)))) ≫
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockFamilyAssembly (power K) n m s ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K (1 + m) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities n m s)).hom ≫
      eqToHom (congrArg (power K) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockArities_sum n m s)) =
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K (n + m) s).hom := by
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.firstBlockFamilyAssembly_power K n m s]
  rw [← tensorHom_def_assoc]
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso_splitAt K n m s

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
