module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyHeadAssembly
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyTensorSplitAt

/-!
模型。文献の定義との比較は後で
# 先頭の組み込みと係数・入力の分離

概要：Berger–Moerdijk §1 の先頭ブロックの合成結果を係数列と入力列へ分ける。
方針：二ブロック再結合との両立を一入力の前半に適用し、単位因子を相殺する。
規約：先頭の係数と入力は既に一つのテンソル対へまとまっている。
使われ方：Schur 作用の生成射の先頭で二段の合成を比較する。
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

/-- 概要：先頭のテンソル対の組み込みは係数列と入力列の独立な組み込みへ分かれる（Berger–Moerdijk §1）。
方針：二ブロック分離の逆射との両立を使い、一次の分離に付く右単位子を除く。
規約：後半の係数・入力の交換には既存の Koszul 対称性を使う。
使われ方：先頭で合成した Schur 生成射の係数と入力を独立に計算する。 -/
lemma tensorFamilyHeadAssembly_tensor (m : ℕ) (V W : Fin (1 + m) → Complex A) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyHeadAssembly m (fun j => V j ⊗ W j) ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso (1 + m) V W).hom =
    ((V ((0 : Fin 1).castAdd m) ⊗ W ((0 : Fin 1).castAdd m)) ◁
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso m (fun j => V (j.natAdd 1)) (fun j => W (j.natAdd 1))).hom) ≫
      tensorμ (V ((0 : Fin 1).castAdd m)) (W ((0 : Fin 1).castAdd m))
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => V (j.natAdd 1)))
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily m (fun j => W (j.natAdd 1))) ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyHeadAssembly m V ⊗ₘ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyHeadAssembly m W) := by
  unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyHeadAssembly
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso_splitAt_inv]
  rw [whiskerRight_comp_tensorHom_assoc]
  erw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso_one_inv]
  rw [tensorHom_def']
  simp only [Category.assoc]
  erw [tensorμ_natural_left_assoc]
  rw [tensorHom_comp_tensorHom]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
