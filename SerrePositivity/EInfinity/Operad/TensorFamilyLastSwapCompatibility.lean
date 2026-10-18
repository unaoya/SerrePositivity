module

public import SerrePositivity.EInfinity.Operad.TensorFamilyLastSwapSeparation
public import SerrePositivity.EInfinity.Operad.SwapPairCoherence

/-!
# 末尾交換と二因子の分離の両立

概要：Berger–Moerdijk §1 の末尾二入力の交換を分離された二因子の対称性と比較する。
方針：二因子の場合は単位子の整合性を使い、先頭を固定した尾への帰納法を用いる。
規約：交換後の分離の終域を元の前半と交換した二因子へ同定する。
使われ方：全入力へのオペラッド合成の外側等変性で末尾交換を比較する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded SerrePositivity.Coxeter

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] tensorFamily
attribute [local implicit_reducible] adjacentTransposition Equiv.swap Equiv.swapCore
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：二因子の交換と末尾二因子の分離は両立する（Berger–Moerdijk §1）。
方針：二因子の分離の単位子による式と交換の単位子の整合性を適用する。
規約：前半は空の族でテンソル単位となる。
使われ方：末尾交換と分離の両立の帰納法の基底に用いる。 -/
lemma tensorFamilySplitLastTwo_lastSwap_zero (V : Fin 2 → Complex A) :
    (tensorFamilyAdjacentIso 1 V (Fin.last 0)).hom ≫
        (tensorFamilySplitLastTwo 0
          (fun i => V (adjacentTransposition (Fin.last 0) i))).hom ≫
        eqToHom (tensorFamily_lastSwap_output_obj 0 V) =
      (tensorFamilySplitLastTwo 0 V).hom ≫
        (tensorFamily 0 (fun i => V i.castSucc.castSucc) ◁ (β_ (V 0) (V 1)).hom) := by
  conv_lhs =>
    arg 1
    change (tensorFamilyAdjacentIso 1 V 0).hom
    rw [tensorFamilyAdjacentIso_zero 0 V]
  conv_lhs =>
    arg 2
    arg 1
    change (tensorFamilySplitLastTwo 0
      (fun i => V (adjacentTransposition (0 : Fin 1) i))).hom
  have h := @swapPair_unit_separation (Complex A) (by infer_instance) (by infer_instance)
    (by infer_instance) (V 0) (V 1)
  simp only [tensorFamilySwapFirstIso,
    tensorFamilySplitLastTwo_zero, tensorFamily, tensorTripleSwapIso,
    Iso.trans_hom, Iso.symm_hom, whiskerRightIso_hom, eqToIso.hom,
    Fin.succ_zero_eq_one, eqToHom_refl,
    Category.comp_id, Category.assoc] at h ⊢
  exact h

/-- 概要：末尾の隣接交換と末尾二因子の分離は両立する（Berger–Moerdijk §1）。
方針：先頭を保つ尾への帰納法を使い、交換後の分離の再帰式と結合子の自然性で比較する。
規約：前半の有限テンソルを固定し、分離した末尾の対に対称性を適用する。
使われ方：反復オペラッド合成の外側等変性で末尾二入力の交換を二位置への合成へ帰着する。 -/
lemma tensorFamilySplitLastTwo_lastSwap (n : ℕ) (V : Fin (n + 2) → Complex A) :
    (tensorFamilyAdjacentIso (n + 1) V (Fin.last n)).hom ≫
        (tensorFamilySplitLastTwo n
          (fun i => V (adjacentTransposition (Fin.last n) i))).hom ≫
        eqToHom (tensorFamily_lastSwap_output_obj n V) =
      (tensorFamilySplitLastTwo n V).hom ≫
        (tensorFamily n (fun i => V i.castSucc.castSucc) ◁
          (β_ (V (Fin.last n).castSucc) (V (Fin.last (n + 1)))).hom) := by
  induction n with
  | zero => exact tensorFamilySplitLastTwo_lastSwap_zero V
  | succ n ih =>
    conv_lhs =>
      arg 1
      change (tensorFamilyAdjacentIso (n + 2) V (Fin.last n).succ).hom
      rw [tensorFamilyAdjacentIso_succ (n + 1) V (Fin.last n)]
    simp only [Category.assoc]
    conv_lhs =>
      arg 2
      rw [tensorFamilySplitLastTwo_lastSwap_succ n V]
    rw [← whiskerLeft_comp_assoc]
    conv_lhs =>
      arg 1
      arg 2
      rw [ih (fun i => V i.succ)]
    have hpost := @splitPair_post_whiskerLeft (Complex A) (by infer_instance)
      (by infer_instance) (V 0) _ _ _ _
      (tensorFamilySplitLastTwo n (fun i => V i.succ)).hom
      (β_ (V (Fin.last n).castSucc.succ) (V (Fin.last (n + 1)).succ)).hom
    dsimp only [tensorFamily, Fin.last, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ]
      at hpost ⊢
    rw [hpost]
    conv_rhs =>
      arg 1
      rw [tensorFamilySplitLastTwo_succ n V]
    dsimp only [tensorFamily, Fin.last, Fin.castSucc, Fin.castAdd, Fin.castLE, Fin.succ]
    simp only [Category.assoc]
    rfl

end SerrePositivity.EInfinity
