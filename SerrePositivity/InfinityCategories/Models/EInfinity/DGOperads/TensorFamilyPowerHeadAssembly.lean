module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyHeadAssembly
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyPowerSplitAt

/-!
模型。文献の定義との比較は後で
# 先頭の入力ブロックを組み込んだ後のテンソル冪の連結

概要：Berger–Moerdijk §1 の二段の全合成で先頭の入力ブロックを連結する。
方針：二ブロックの再結合との両立と、一入力の連結の単位則を使う。
規約：後半の入力順序を保存し、先頭と後半の長さが零の場合を含む。
使われ方：内側で連結した入力を外側の全合成の入力へ送る。
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

/-- 概要：二ブロックを再結合した後の連結は各ブロックの連結を通して計算できる（Berger–Moerdijk §1）。
方針：二ブロック分離との両立に分離の逆射を前置して相殺する。
規約：総 arity は元の族の和に戻す。
使われ方：先頭演算の入力と後半の入力族を再結合してから連結する。 -/
lemma tensorPowerFamilyIso_splitAt_inv (K : Complex A) (n m : ℕ) (s : Fin (n + m) → ℕ) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt n m (fun j => power K (s j))).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K (n + m) s).hom =
    ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K n (fun j => s (j.castAdd m))).hom ⊗ₘ
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K m (fun j => s (j.natAdd n))).hom) ≫
      (appendIso K (∑ j : Fin n, s (j.castAdd m)) (∑ j : Fin m, s (j.natAdd n))).hom ≫
      eqToHom (congrArg (power K) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_sum_splitAt n m s).symm) := by
  have h := congrArg ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitAt n m (fun j => power K (s j))).inv ≫ ·)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso_splitAt K n m s)
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using h.symm

/-- 概要：先頭の入力ブロックを組み込んだ後の連結は先頭と後半を連結する射となる（Berger–Moerdijk §1）。
方針：二ブロックの再結合の式で前半を一入力とし、右単位子を相殺する。
規約：出力は全入力族の arity の和へ移送する。
使われ方：自由代数の部分合成則で内側と外側の入力の連結を比較する。 -/
lemma tensorPowerFamilyIso_headAssembly (K : Complex A) (m : ℕ) (s : Fin (1 + m) → ℕ) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyHeadAssembly m (fun j => power K (s j)) ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K (1 + m) s).hom =
    (power K (s ((0 : Fin 1).castAdd m)) ◁
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso K m (fun j => s (j.natAdd 1))).hom) ≫
      (appendIso K (s ((0 : Fin 1).castAdd m)) (∑ j : Fin m, s (j.natAdd 1))).hom ≫
      eqToHom (congrArg (power K) (by
        have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_sum_splitAt 1 m s
        simpa only [Fin.sum_univ_one] using h.symm :
          s ((0 : Fin 1).castAdd m) + (∑ j : Fin m, s (j.natAdd 1)) = ∑ j, s j)) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyHeadAssembly
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso_splitAt_inv]
  rw [whiskerRight_comp_tensorHom_assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorPowerFamilyIso_one]
  simp only [Iso.inv_hom_id_assoc]
  rw [tensorHom_def']
  simp only [Category.assoc]
  rw [appendIso_index_left_assoc K
    (by simp : s ((0 : Fin 1).castAdd m) = ∑ j : Fin 1, s (j.castAdd m))]
  simp only [eqToHom_trans]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
