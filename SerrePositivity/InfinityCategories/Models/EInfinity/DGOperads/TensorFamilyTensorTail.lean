module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyTensorTransport
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyAdjacentTail

/-!
模型。文献の定義との比較は後で
# 尾の隣接交換後のテンソル分離

概要：Berger–Moerdijk §1 の先頭を固定した交換の後の分離同型を尾で表す。
方針：ずらした置換を cases の添字族に移し、分離同型の先頭の再帰を計算する。
規約：係数列と入力列の先頭はそれぞれ固定する。
使われ方：分離同型と任意の隣接交換の可換性の帰納段階に用いる。
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
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：尾の交換後の分離は先頭を固定した尾の分離と tensorμ で計算できる（Berger–Moerdijk §1）。
方針：交換後の族を先頭と尾の cases の族へ比較し、分離の再帰を一回計算する。
規約：対象の移送は始域と分離後の両列に明示する。
使われ方：隣接位置を一つずらす帰納段階で添字の移送を除く。 -/
lemma tensorFamilyTensorIso_adjacentSucc_transport (n : ℕ)
    (V W : Fin (n + 2) → Complex A) (i : Fin n) :
    eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_adjacentSucc_obj n (fun j => V j ⊗ W j) i).symm ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso (n + 2) (fun j => V (adjacentTransposition i.succ j))
        (fun j => W (adjacentTransposition i.succ j))).hom ≫
      (eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_adjacentSucc_obj n V i) ⊗ₘ
        eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_adjacentSucc_obj n W i)) =
    ((V 0 ⊗ W 0) ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso (n + 1)
      (fun j => V (adjacentTransposition i j).succ)
      (fun j => W (adjacentTransposition i j).succ)).hom) ≫
      tensorμ (V 0) (W 0)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 1) (fun j => V (adjacentTransposition i j).succ))
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 1) (fun j => W (adjacentTransposition i j).succ)) := by
  have hi : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorTailPermutationIndex (n + 1) (adjacentTransposition i) =
      fun j => adjacentTransposition i.succ j :=
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorTailPermutationIndex_eq (n + 1) (adjacentTransposition i)).trans
      (congrArg (fun σ : Equiv.Perm (Fin (n + 2)) => fun j => σ j) (shiftPerm_adjacent n i))
  have hV : (fun j => V (adjacentTransposition i.succ j)) =
      (fun j => V (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorTailPermutationIndex (n + 1) (adjacentTransposition i) j)) :=
    congrArg (fun f => fun j => V (f j)) hi.symm
  have hW : (fun j => W (adjacentTransposition i.succ j)) =
      (fun j => W (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorTailPermutationIndex (n + 1) (adjacentTransposition i) j)) :=
    congrArg (fun f => fun j => W (f j)) hi.symm
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso_compare (n + 2) hV hW
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_adjacentSucc_obj n (fun j => V j ⊗ W j) i) (by rfl)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_adjacentSucc_obj n V i) (by rfl)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_adjacentSucc_obj n W i) (by rfl)
  conv_rhs at h =>
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorTailPermutationIndex, Fin.cases_zero, Fin.cases_succ,
      Iso.trans_hom, whiskerLeftIso_hom, eqToHom_refl, tensorHom_id,
      id_whiskerRight, Category.id_comp, Category.comp_id]
  exact h

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
