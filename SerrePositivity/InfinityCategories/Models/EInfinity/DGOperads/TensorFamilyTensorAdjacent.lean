module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyTensorFirstSwap
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyTensorTail

/-!
模型。文献の定義との比較は後で
# 有限テンソル族の分離と任意の隣接交換

概要：Berger–Moerdijk §1 の自由代数の外側交換を係数列と入力列へ分離する。
方針：先頭交換の可換性を基底とし、先頭を固定する尾の交換へ帰納する。
規約：隣接する二つの対を同時に交換する。
使われ方：Schur 作用の生成射の外側等変性を任意の隣接位置で証明する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads

open _root_.CategoryTheory _root_.CategoryTheory.MonoidalCategory
open _root_.SerrePositivity.DifferentialGraded _root_.SerrePositivity.Coxeter

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso

/-- 概要：任意の隣接する対の交換は分離後の二列の隣接交換になる（Berger–Moerdijk §1）。
方針：交換後の対象の移送を相殺し、尾の帰納仮定と tensorμ の自然性を用いる。
規約：n+1 個の対に n 個の隣接交換位置を指定する。
使われ方：Schur 演算の係数側とテンソル冪側の等変性を組み合わせる。 -/
lemma tensorFamilyTensorIso_adjacent (n : ℕ) (V W : Fin (n + 1) → Complex A) (i : Fin n) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso n (fun j => V j ⊗ W j) i).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso (n + 1) (fun j => V (adjacentTransposition i j))
        (fun j => W (adjacentTransposition i j))).hom =
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso (n + 1) V W).hom ≫
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso n V i).hom ⊗ₘ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso n W i).hom) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso_zero]
      exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso_firstSwap n V W
    · apply (cancel_mono (eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_adjacentSucc_obj n V j) ⊗ₘ
        eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_adjacentSucc_obj n W j))).1
      simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso_succ, Category.assoc]
      conv_lhs =>
        arg 2
        rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso_adjacentSucc_transport]
      rw [← whiskerLeft_comp_assoc]
      conv_lhs =>
        arg 1
        arg 2
        rw [ih (fun j => V j.succ) (fun j => W j.succ) j]
      simp only [whiskerLeft_comp, Category.assoc]
      conv_lhs =>
        arg 2
        rw [tensorμ_natural_right]
      conv_rhs =>
        arg 1
        unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso
        simp only [Iso.trans_hom, whiskerLeftIso_hom]
      simp only [Category.assoc, ← tensorHom_comp_tensorHom]
      conv_rhs =>
        arg 2
        arg 2
        arg 2
        rw [tensorHom_comp_tensorHom]
        simp only [eqToHom_trans, eqToHom_refl, tensorHom_id, id_whiskerRight]
      simp only [Category.comp_id]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
