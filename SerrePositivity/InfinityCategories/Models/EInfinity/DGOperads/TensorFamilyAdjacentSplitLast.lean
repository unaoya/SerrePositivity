module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.AdjacentTailSplitLastTransport

/-!
模型。文献の定義との比較は後で
# 末尾を固定する隣接交換と最後の分離の可換性

概要：Berger–Moerdijk §1 の反復合成の帰納法で、隣接交換を最後の因子の分離に通す。
方針：先頭交換を基底とし、先頭を保った尾の交換へ帰納する。
規約：最後の因子は交換せず、前半の n+1 入力の隣接二位置を交換する。
使われ方：反復合成の外側等変性を末尾以外の隣接位置へ帰納的に拡張する。
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
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast

/-- 概要：末尾を固定する任意の隣接交換と最後の因子の分離は両立する（Berger–Moerdijk §1）。
方針：先頭交換と尾の交換で場合分けし、分離の再帰式と結合子の中央の自然性を使う。
規約：交換後の分離の終域を前半の交換後の族と元の最後の因子へ移す。
使われ方：前方への反復合成の任意の隣接位置の外側等変性の帰納段階に用いる。 -/
lemma tensorFamilySplitLast_adjacent (n : ℕ) (V : Fin (n + 2) → Complex A) (i : Fin n) :
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso (n + 1) V i.castSucc).hom ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast (n + 1) (fun j => V (adjacentTransposition i.castSucc j))).hom ≫
        eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_adjacentCastSucc_output_obj n V i) =
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast (n + 1) V).hom ≫
        ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso n (fun j => V j.castSucc) i).hom ▷ V (Fin.last (n + 1))) := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast_adjacent_zero n V
    · apply (cancel_mono
        (eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_adjacentSucc_obj n (fun j => V j.castSucc) i) ▷
          V (Fin.last (n + 2)))).1
      simp only [Category.assoc]
      conv_lhs =>
        arg 2
        arg 2
        erw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentSucc_splitLast_output_hom n V i]
      conv_lhs =>
        arg 1
        change (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso (n + 2) V i.castSucc.succ).hom
        rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso_succ (n + 1) V i.castSucc]
      simp only [Category.assoc]
      conv_lhs =>
        arg 2
        erw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentSucc_splitLast_rec n V i]
      rw [← whiskerLeft_comp_assoc]
      conv_lhs =>
        arg 1
        arg 2
        rw [ih (fun j => V j.succ) i]
      conv_rhs =>
        arg 2
        rw [← comp_whiskerRight]
        arg 1
        erw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso_succ n (fun j => V j.castSucc) i]
        simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
      conv_rhs =>
        arg 1
        rw [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast_succ (n + 1) V]
      have hn := associator_inv_naturality_middle (V 0)
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso n (fun j => V j.castSucc.succ) i).hom
        (V (Fin.last (n + 2)))
      have h := congrArg ((V 0 ◁
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast (n + 1) (fun j => V j.succ)).hom) ≫ ·) hn
      dsimp only [_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily, Fin.last, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ]
        at h ⊢
      simp only [whiskerLeft_comp, Category.assoc]
      exact h

/-- 概要：外側の係数射を伴う末尾固定の隣接交換は最後の分離と両立する（Berger–Moerdijk §1）。
方針：テンソル積の合成則で入力族の射をまとめ、隣接交換と分離の可換性を適用する。
規約：最後の因子には恒等射を作用させる。
使われ方：部分合成と残りの反復合成の等変性を結ぶ再帰の一段に用いる。 -/
@[reassoc]
lemma tensorFamilySplitLast_adjacent_outer (n : ℕ) (V : Fin (n + 2) → Complex A)
    (i : Fin n) {R : Complex A} (a : R ⟶ R) :
    (a ⊗ₘ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso (n + 1) V i.castSucc).hom) ≫
        (R ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast (n + 1)
          (fun j => V (adjacentTransposition i.castSucc j))).hom) ≫
        (R ◁ eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_adjacentCastSucc_output_obj n V i)) =
      (R ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast (n + 1) V).hom) ≫
        (a ⊗ₘ ((_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyAdjacentIso n (fun j => V j.castSucc) i).hom ⊗ₘ
          𝟙 (V (Fin.last (n + 1))))) := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast_adjacent n V i
  simp only [← tensorHom_id] at h
  simp only [← id_tensorHom, tensorHom_comp_tensorHom, Category.id_comp, Category.comp_id]
  rw [h]

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
