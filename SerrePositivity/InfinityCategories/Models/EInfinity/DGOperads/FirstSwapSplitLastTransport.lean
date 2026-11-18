module

public import SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.FirstSwapSplitLastFamily

/-!
模型。文献の定義との比較は後で
# 先頭交換後の最後の分離の移送と展開

概要：Berger–Moerdijk §1 の先頭交換と最後の分離を、交換した先頭二因子を明示した式で比較する。
方針：具体的な入力族へ移し、分離の二段の再帰式を適用する。
規約：最後の因子を固定し、交換後の前半のテンソルの対象を具体化する。
使われ方：四因子のモノイダル整合性から先頭交換と分離の可換性を導く。
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

attribute [local implicit_reducible] _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyFirstSwapFamily
  Fin.cases Fin.induction Fin.induction.go
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast

/-- 概要：先頭交換後の分離の終域は交換した二因子と残りの前半、最後の因子で表せる（Berger–Moerdijk §1）。
方針：持ち上げた隣接交換の終域を同定し、前半の先頭交換のテンソル対象を展開する。
規約：族の長さは n+3 で最後の因子は固定する。
使われ方：実際の先頭交換後の分離の終域を四因子の整合性の終域へ移す。 -/
lemma tensorFamilyFirstSwap_splitLast_output_obj (n : ℕ) (V : Fin (n + 3) → Complex A) :
    _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily (n + 2) (fun i =>
        V (adjacentTransposition (0 : Fin (n + 2)) i.castSucc)) ⊗
        V (adjacentTransposition (0 : Fin (n + 2)) (Fin.last (n + 2))) =
      (V 1 ⊗ (V 0 ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc.succ.succ))) ⊗
        V (Fin.last (n + 2)) := by
  have h := (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_adjacentCastSucc_output_obj (n + 1) V 0).trans
    (congrArg (fun X : Complex A => X ⊗ V (Fin.last (n + 2)))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_firstSwap_obj n (fun i => V i.castSucc)))
  exact h

/-- 概要：交換後の分離の二つの終域の移送は具体的な四因子の対象への一つの移送に一致する（Berger–Moerdijk §1）。
方針：テンソルの右への移送と等式の射の合成を整理する。
規約：前半の先頭交換の対象の同定を最後の因子の左側に適用する。
使われ方：先頭交換と分離の可換性を同型による後合成で比較する。 -/
lemma tensorFamilyFirstSwap_splitLast_output_hom (n : ℕ) (V : Fin (n + 3) → Complex A) :
    eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_adjacentCastSucc_output_obj (n + 1) V 0) ≫
        (eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_firstSwap_obj n (fun i => V i.castSucc)) ▷
          V (Fin.last (n + 2))) =
      eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyFirstSwap_splitLast_output_obj n V) := by
  conv_lhs =>
    arg 2
    rw [eqToHom_whiskerRight (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_firstSwap_obj n (fun i => V i.castSucc))
      (V (Fin.last (n + 2)))]
  exact eqToHom_trans (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_adjacentCastSucc_output_obj (n + 1) V 0)
    (congrArg (fun X : Complex A => X ⊗ V (Fin.last (n + 2)))
      (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_firstSwap_obj n (fun i => V i.castSucc)))

/-- 概要：実際の先頭交換後の最後の分離は具体的な交換後の入力族の分離に一致する（Berger–Moerdijk §1）。
方針：等しい入力族の分離の比較を、具体的な始域と終域に適用する。
規約：始域は交換した先頭二因子と元の尾、終域は最後の因子を分離した四因子の対象。
使われ方：先頭交換の後の分離を再帰定義で展開できる形に移す。 -/
lemma tensorFamilyFirstSwap_splitLast_compare (n : ℕ) (V : Fin (n + 3) → Complex A) :
    eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_firstSwap_obj (n + 1) V).symm ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast (n + 2)
          (fun i => V (adjacentTransposition (0 : Fin (n + 2)) i))).hom ≫
        eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyFirstSwap_splitLast_output_obj n V) =
      eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyFirstSwapFamily_source_obj (n + 1) V).symm ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast (n + 2) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyFirstSwapFamily (n + 1) V)).hom ≫
        eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyFirstSwapFamily_output_obj n V) := by
  exact _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast_compare (n + 2) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyFirstSwapFamily_eq (n + 1) V)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyFirstSwapFamily_source_obj (n + 1) V)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily_firstSwap_obj (n + 1) V)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyFirstSwapFamily_output_obj n V)
    (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyFirstSwap_splitLast_output_obj n V)

/-- 概要：具体的な先頭交換後の最後の分離は交換した二因子を保つ尾の分離で計算できる（Berger–Moerdijk §1）。
方針：最後の分離の先頭二段の展開を具体的な入力族へ適用する。
規約：分離した最後の因子の前に、交換した先頭二因子と残りの前半を置く。
使われ方：先頭交換と分離の可換性の基底を一般の四因子の整合性へ帰着する。 -/
lemma tensorFamilyFirstSwapFamily_splitLast_expand (n : ℕ)
    (V : Fin (n + 3) → Complex A) :
    eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyFirstSwapFamily_source_obj (n + 1) V).symm ≫
        (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast (n + 2) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyFirstSwapFamily (n + 1) V)).hom ≫
        eqToHom (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyFirstSwapFamily_output_obj n V) =
      (V 1 ◁ (V 0 ◁ (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast n (fun i => V i.succ.succ)).hom)) ≫
        (V 1 ◁ (α_ (V 0) (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc.succ.succ))
          (V (Fin.last (n + 2)))).inv) ≫
        (α_ (V 1) (V 0 ⊗ _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamily n (fun i => V i.castSucc.succ.succ))
          (V (Fin.last (n + 2)))).inv := by
  have h := _root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilySplitLast_two_head n (_root_.SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads.tensorFamilyFirstSwapFamily (n + 1) V)
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact h

end SerrePositivity.InfinityCategories.Models.EInfinity.DGOperads
