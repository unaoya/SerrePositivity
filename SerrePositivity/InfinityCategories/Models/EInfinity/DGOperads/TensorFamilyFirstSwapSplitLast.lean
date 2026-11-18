module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.FirstSwapSplitLastTransport
public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.SwapSplitLastCoherence

/-!
模型。文献の定義との比較は後で
# 先頭交換と最後の因子の分離の可換性

概要：Berger–Moerdijk §1 の末尾を固定する隣接交換について、先頭二因子の場合を証明する。
方針：交換後の入力族の比較で始域・終域を具体化し、四因子の整合性を適用する。
規約：三つ以上の入力を持ち、最後の因子は交換しない。
使われ方：任意の隣接交換と最後の分離の可換性の帰納法の基底に用いる。
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

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily adjacentTransposition Equiv.swap Equiv.swapCore
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast

/-- 概要：先頭二因子の交換と最後の因子の分離は両立する（Berger–Moerdijk §1）。
方針：交換後の終域の同型で後合成して比較し、交換射の自然性と四因子の整合性に帰着する。
規約：交換後の分離の終域を、元の前半の先頭交換と最後の因子のテンソルへ同定する。
使われ方：末尾を固定する任意の隣接交換の可換性の先頭の場合を与える。 -/
lemma tensorFamilySplitLast_adjacent_zero (n : ℕ) (V : Fin (n + 3) → Complex A) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso (n + 2) V (0 : Fin (n + 1)).castSucc).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast (n + 2)
          (fun j => V (adjacentTransposition (0 : Fin (n + 1)).castSucc j))).hom ≫
        eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_adjacentCastSucc_output_obj (n + 1) V 0) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast (n + 2) V).hom ≫
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso (n + 1) (fun j => V j.castSucc) 0).hom ▷
          V (Fin.last (n + 2))) := by
  apply (cancel_mono (eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_firstSwap_obj n (fun i => V i.castSucc)) ▷
    V (Fin.last (n + 2)))).1
  simp only [Category.assoc]
  conv_lhs =>
    arg 2
    arg 2
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyFirstSwap_splitLast_output_hom n V]
  conv_lhs =>
    arg 1
    change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso (n + 2) V 0).hom
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso_zero (n + 1) V]
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySwapFirstIso, Iso.trans_hom, eqToIso.hom]
  simp only [Category.assoc]
  conv_lhs =>
    arg 2
    erw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyFirstSwap_splitLast_compare n V,
      _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyFirstSwapFamily_splitLast_expand n V]
  conv_rhs =>
    arg 2
    rw [← comp_whiskerRight]
    arg 1
    erw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso_zero n (fun i => V i.castSucc)]
    simp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySwapFirstIso, Iso.trans_hom, eqToIso.hom, Category.assoc,
      eqToHom_trans, eqToHom_refl, Category.comp_id]
  conv_rhs =>
    arg 1
    rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast_two_head n V]
  have hn := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorTripleSwapIso_naturality (𝟙 (V 0)) (𝟙 (V 1))
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n (fun i => V i.succ.succ)).hom
  simp only [id_tensorHom] at hn
  have hn' := congrArg (fun f => f ≫
    (V 1 ◁ (α_ (V 0) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc.succ.succ))
      (V (Fin.last (n + 2)))).inv) ≫
    (α_ (V 1) (V 0 ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc.succ.succ))
      (V (Fin.last (n + 2)))).inv) hn.symm
  have hc :
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorTripleSwapIso (V 0) (V 1)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc.succ.succ) ⊗ V (Fin.last (n + 2)))).hom ≫
          (V 1 ◁ (α_ (V 0) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc.succ.succ))
            (V (Fin.last (n + 2)))).inv) ≫
          (α_ (V 1) (V 0 ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc.succ.succ))
            (V (Fin.last (n + 2)))).inv =
        (V 0 ◁ (α_ (V 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc.succ.succ))
          (V (Fin.last (n + 2)))).inv) ≫
          (α_ (V 0) (V 1 ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc.succ.succ))
            (V (Fin.last (n + 2)))).inv ≫
          ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorTripleSwapIso (V 0) (V 1)
            (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc.succ.succ))).hom ▷ V (Fin.last (n + 2))) := by
    simpa only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorTripleSwapIso, Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom,
      Category.assoc] using
      (@_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.frontSwap_splitLast_coherence (Complex A) (by infer_instance) (by infer_instance)
        (by infer_instance) (V 0) (V 1) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc.succ.succ))
          (V (Fin.last (n + 2))))
  have hc' := congrArg ((V 0 ◁ (V 1 ◁
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n (fun i => V i.succ.succ)).hom)) ≫ ·) hc
  simp only [Category.assoc] at hn' hc' ⊢
  dsimp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily, Fin.last, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ]
    at hn' hc' ⊢
  exact hn'.trans hc'

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
