module

public import SerrePositivity.EInfinity.Operad.TensorFamilySplitAtNaturality
public import Mathlib.Tactic.CategoryTheory.Monoidal.Basic

/-!
# 有限テンソル族の二部分への分離の境界の場合

概要：Berger–Moerdijk §1 のブロック分離を既存の末尾一因子の分離へ接続する。
方針：後半一因子の場合の再帰を計算し、単位子と結合子の整合性を使う。
規約：後半の有限テンソルに残る単位因子を右単位子で除く。
使われ方：新しい任意位置の分離と既存の反復合成の末尾分離を比較する。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity

open CategoryTheory MonoidalCategory
open SerrePositivity.DifferentialGraded

variable {A : Type u} [CommRing A]

attribute [local implicit_reducible] tensorFamily
attribute [local irreducible] HomologicalComplex.monoidalCategoryStruct

/-- 概要：後半一因子への分離は単位因子を除くと既存の末尾分離に一致する（Berger–Moerdijk §1）。
方針：分離の再帰を一回展開し、三つの単位子と結合子を相殺する。
規約：末尾の入力の添字は last n。
使われ方：二部分への分離を末尾からの反復代入に接続する。 -/
lemma tensorFamilySplitAt_one (n : ℕ) (V : Fin (n + 1) → Complex A) :
    (tensorFamilySplitAt n 1 V).hom ≫
      (tensorFamily n (fun j => V (j.castAdd 1)) ◁ (ρ_ (V (Fin.last n))).hom) =
    (tensorFamilySplitLast n V).hom := by
  apply (cancel_epi (tensorFamilySplitLast n V).inv).1
  simp only [tensorFamilySplitAt, tensorFamilySplitLast, Nat.add_zero,
    Iso.trans_hom, Iso.symm_hom, Iso.trans_inv, Iso.symm_inv,
    whiskerRightIso_hom, whiskerLeftIso_hom, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id]
  dsimp only [tensorFamily]
  monoidal

end SerrePositivity.EInfinity
