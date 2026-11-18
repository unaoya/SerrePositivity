module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorSeparationTripleSwap
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyAdjacentGenerators

/-!
模型。文献の定義との比較は後で
# テンソル族の分離の添字の移送

概要：Berger–Moerdijk §1 の先頭交換後の分離同型を具体的な二因子と尾で記述する。
方針：等しい二つの添字族の分離同型を比較し、先頭交換を cases の表示へ移す。
規約：係数列と入力列の対象の移送をそれぞれ明示する。
使われ方：分離同型と隣接交換の可換性を証明する。
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

/-- 概要：等しい二つの複体族の分離同型は対象の移送後に一致する（Berger–Moerdijk §1）。
方針：族の等式で同一視し、等式の証明の一意性を用いる。
規約：始域と分離後の二つの対象を独立に指定する。
使われ方：交換後の添字の具体的な表示へ分離同型を移す。 -/
lemma tensorFamilyTensorIso_compare (n : ℕ) {V W V' W' : Fin n → Complex A}
    (hV : V = V') (hW : W = W') {D E F : Complex A}
    (hs : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i ⊗ W i) = D)
    (hs' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V' i ⊗ W' i) = D)
    (hv : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n V = E) (hv' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n V' = E)
    (hw : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n W = F) (hw' : _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n W' = F) :
    eqToHom hs.symm ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso n V W).hom ≫ (eqToHom hv ⊗ₘ eqToHom hw) =
      eqToHom hs'.symm ≫ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso n V' W').hom ≫
        (eqToHom hv' ⊗ₘ eqToHom hw') := by
  subst V'
  subst W'
  rfl

/-- 概要：先頭交換後の分離同型は交換した二対と残りの族の分離から構成される（Berger–Moerdijk §1）。
方針：先頭交換の添字を cases の表示へ移し、分離同型の再帰を二回計算する。
規約：始域と分離後の両列を先頭二因子と尾に同定する。
使われ方：先頭交換と分離の可換性で arity の添字の移送を除く。 -/
lemma tensorFamilyTensorIso_firstSwap_transport (n : ℕ) (V W : Fin (n + 2) → Complex A) :
    eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_firstSwap_obj n (fun i => V i ⊗ W i)).symm ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso (n + 2) (fun j => V (adjacentTransposition (0 : Fin (n + 1)) j))
        (fun j => W (adjacentTransposition (0 : Fin (n + 1)) j))).hom ≫
      (eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_firstSwap_obj n V) ⊗ₘ
        eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_firstSwap_obj n W)) =
    ((V 1 ⊗ W 1) ◁ ((V 0 ⊗ W 0) ◁
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso n (fun j => V j.succ.succ) (fun j => W j.succ.succ)).hom)) ≫
      ((V 1 ⊗ W 1) ◁ tensorμ (V 0) (W 0)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => V j.succ.succ)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => W j.succ.succ))) ≫
      tensorμ (V 1) (W 1)
        (V 0 ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => V j.succ.succ))
        (W 0 ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => W j.succ.succ)) := by
  have hV : (fun j => V (adjacentTransposition (0 : Fin (n + 1)) j)) =
      (fun j => V (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFirstSwapIndex n j)) :=
    congrArg (fun f => fun j => V (f j)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFirstSwapIndex_eq n).symm
  have hW : (fun j => W (adjacentTransposition (0 : Fin (n + 1)) j)) =
      (fun j => W (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFirstSwapIndex n j)) :=
    congrArg (fun f => fun j => W (f j)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFirstSwapIndex_eq n).symm
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso_compare (n + 2) hV hW
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_firstSwap_obj n (fun i => V i ⊗ W i)) (by rfl)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_firstSwap_obj n V) (by rfl)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_firstSwap_obj n W) (by rfl)
  conv_rhs at h =>
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso, _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFirstSwapIndex, Fin.cases_zero, Fin.cases_succ,
      Iso.trans_hom, whiskerLeftIso_hom, eqToHom_refl, tensorHom_id,
      id_whiskerRight, Category.id_comp, Category.comp_id, whiskerLeft_comp, Category.assoc]
  exact h

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
