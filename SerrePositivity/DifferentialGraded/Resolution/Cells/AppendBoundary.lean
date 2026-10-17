module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.AppendBoundaryRecursion

/-! # 左有限pathを固定した連結の境界置換Leibniz則

## 概要
左有限pathを固定した連結の境界置換Leibniz則。

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
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

lemma appendRight_replacement (w : List I) (x y z : D) :
    (Cochain.ofHom (C.appendRight A D I w x y z)).comp (C.replacement A D I x z) (zero_add 1) =
    ((tensorRightHom (C.internalHom A D I y z) _ _).f 1 (C.replaceRow A D I w x y)).comp
      (Cochain.ofHom (C.internalComposition A D I x y z)) (add_zero 1) +
    ((tensorLeftHom (C.term A D I w x y) _ _).f 1 (C.replacement A D I y z)).comp
      (Cochain.ofHom (C.appendRight A D I w x y z)) (add_zero 1) := by
  induction w generalizing x with
  | nil =>
    rw [replaceRow_nil, map_zero, Cochain.zero_comp, zero_add]
    exact C.internalPrepend_replacement A D I x y z
  | cons b w ih =>
    rw [appendRight_replacement_cons, ih (C.target b), appendLiftCochain_add,
      ← appendLiftCochain_left, ← appendLiftCochain_right, replaceRow_cons, map_add]
    rw [Cochain.add_comp _ _ _ (add_zero 1)]
    rw [tensorRightHom_cochain_comp, tensorRightHom_ofHom,
      Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp,
      internalComposition_left_inclusion]
    exact (add_assoc _ _ _).symm

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
