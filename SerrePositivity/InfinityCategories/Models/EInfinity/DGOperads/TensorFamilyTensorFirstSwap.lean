module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.TensorFamilyTensorTransport

/-!
模型。文献の定義との比較は後で
# 有限テンソル族の分離と先頭交換

概要：Berger–Moerdijk §1 の自由代数の先頭交換を係数列と入力列の交換に分離する。
方針：最後の族の分離を交換の前へ移し、三つの対の先頭交換の可換性を使う。
規約：添字の移送は既存の有限族の先頭交換の同型に含める。
使われ方：任意の隣接位置の交換についての帰納法の基底となる。
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

/-- 概要：有限族の先頭二対の交換は分離後の二列の先頭交換になる（Berger–Moerdijk §1）。
方針：交換後の対象の移送を相殺し、尾の分離の自然性と三対の交換の可換性を組み合わせる。
規約：残りの n 個の対の順序を保つ。
使われ方：Schur 作用の隣接交換の外側等変性の先頭の場合を証明する。 -/
lemma tensorFamilyTensorIso_firstSwap (n : ℕ) (V W : Fin (n + 2) → Complex A) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySwapFirstIso n (fun j => V j ⊗ W j)).hom ≫
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso (n + 2)
        (fun j => V (adjacentTransposition (0 : Fin (n + 1)) j))
        (fun j => W (adjacentTransposition (0 : Fin (n + 1)) j))).hom =
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso (n + 2) V W).hom ≫
      ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySwapFirstIso n V).hom ⊗ₘ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySwapFirstIso n W).hom) := by
  apply (cancel_mono (eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_firstSwap_obj n V) ⊗ₘ
    eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_firstSwap_obj n W))).1
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySwapFirstIso, Iso.trans_hom, eqToIso.hom, Category.assoc]
  conv_lhs =>
    arg 2
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso_firstSwap_transport]
  have hn := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorTripleSwapIso_naturality (𝟙 (V 0 ⊗ W 0)) (𝟙 (V 1 ⊗ W 1))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso n (fun j => V j.succ.succ) (fun j => W j.succ.succ)).hom
  simp only [id_tensorHom] at hn
  rw [← Category.assoc _ _ (((V 1 ⊗ W 1) ◁ tensorμ (V 0) (W 0)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => V j.succ.succ)) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun j => W j.succ.succ))) ≫ _),
    ← hn]
  simp only [Category.assoc]
  rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorTripleSwapIso_separation]
  conv_rhs =>
    arg 1
    unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso
    simp only [Iso.trans_hom, whiskerLeftIso_hom, whiskerLeft_comp, Category.assoc]
  simp only [Category.assoc, eqToHom_refl, tensorHom_id, id_whiskerRight, Category.comp_id]
  conv_rhs =>
    arg 1
    arg 2
    unfold _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyTensorIso
    simp only [Iso.trans_hom, whiskerLeftIso_hom]
  simp only [whiskerLeft_comp, Category.assoc]
  simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily]
  rfl

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
