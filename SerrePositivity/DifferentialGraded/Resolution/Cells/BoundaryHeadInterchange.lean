module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.BoundaryNaturality

/-! # 先頭生成元と任意後方生成元の境界置換の反交換

## 概要
先頭生成元と任意後方生成元の境界置換の反交換。

## 方針
有限pathとcellの段階構成、明示的chain map、余極限を使って標準分解を積み上げる。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。任意可換環上のK-flat dg圏分解の構成部品。Hom非平坦のMorita・
tensorやM9で平坦性が崩れた場合の再開に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w)
variable (C : Family A D I)
attribute [local irreducible] replaceHead replaceFirst replaceFace

lemma replaceHead_face_anticommute (i : I) (w : List I) (j : ℕ) (y : D) :
    (C.replaceHead A D I i w y).comp (C.replaceFace A D I w j (C.source i) y)
      (show (1 : ℤ) + 1 = 2 by omega) =
    -(((tensorLeftHom (C.generator A D I i) _ _).f 1
      (C.replaceFace A D I w j (C.target i) y)).comp
      (C.replaceHead A D I i (w.eraseIdx j) y) (show (1 : ℤ) + 1 = 2 by omega)) := by
  rw [replaceHead, replaceHead, Cochain.comp_assoc_of_second_is_zero_cochain,
    prependMap_replaceFace, ← Cochain.comp_assoc_of_third_is_zero_cochain,
    tensorCochain_odd_anticommute, Cochain.neg_comp,
    Cochain.comp_assoc_of_third_is_zero_cochain]

lemma replaceFirst_face_anticommute (i : I) (w : List I) (j : ℕ) (x y : D) :
    (C.replaceFirst A D I i w x y).comp (C.replaceFace A D I w j x y)
      (show (1 : ℤ) + 1 = 2 by omega) =
    -((C.replaceFace A D I (i :: w) (j + 1) x y).comp
      (C.replaceFirst A D I i (w.eraseIdx j) x y) (show (1 : ℤ) + 1 = 2 by omega)) := by
  rw [replaceFace_succ, replaceFirst_eq_head, replaceFirst_eq_head,
    Cochain.comp_assoc_of_second_is_zero_cochain, prependMap_replaceFace,
    ← Cochain.comp_assoc_of_third_is_zero_cochain,
    ← tensorLeftHom_cochain_comp, replaceHead_face_anticommute, map_neg,
    tensorLeftHom_cochain_comp, Cochain.neg_comp,
    Cochain.comp_assoc_of_third_is_zero_cochain]

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
