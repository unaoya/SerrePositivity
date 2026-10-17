module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.AppendRightAssociativity
public import SerrePositivity.DifferentialGraded.Complexes.TensorRightTwoCoproductExt

/-! # 任意次数cell path：InternalAssociativity

## 概要
任意次数cell path：InternalAssociativity。

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
open CategoryTheory Limits MonoidalCategory HomologicalComplex CochainComplex HomComplex
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

lemma internalComposition_assoc (x y z t : D) :
    (C.internalComposition A D I x y z ▷ C.internalHom A D I z t) ≫
      C.internalComposition A D I x z t =
    (α_ (C.internalHom A D I x y) (C.internalHom A D I y z) (C.internalHom A D I z t)).hom ≫
      C.internalHom A D I x y ◁ C.internalComposition A D I y z t ≫
        C.internalComposition A D I x y t := by
  apply tensorRightTwoCoproduct_hom_ext (fun w : List I => C.term A D I w x y)
    (C.internalHom A D I y z) (C.internalHom A D I z t) (C.internalHom A D I x t)
  intro w
  change ((C.inclusion A D I w x y ▷ C.internalHom A D I y z) ▷ C.internalHom A D I z t) ≫
      (C.internalComposition A D I x y z ▷ C.internalHom A D I z t) ≫
        C.internalComposition A D I x z t = _
  rw [← comp_whiskerRight_assoc, internalComposition_left_inclusion,
    associator_naturality_left_assoc, ← whisker_exchange_assoc]
  change (C.appendRight A D I w x y z ▷ C.internalHom A D I z t) ≫
      C.internalComposition A D I x z t =
    (α_ (C.term A D I w x y) (C.internalHom A D I y z) (C.internalHom A D I z t)).hom ≫
      (C.term A D I w x y) ◁ C.internalComposition A D I y z t ≫
        (C.inclusion A D I w x y ▷ C.internalHom A D I y t) ≫ C.internalComposition A D I x y t
  rw [internalComposition_left_inclusion, appendRight_assoc]

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
