module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.AppendRecursion
public import SerrePositivity.DifferentialGraded.Resolution.Cells.AppendPrepend

/-! # 任意次数cell path：AppendRightPrepend

## 概要
任意次数cell path：AppendRightPrepend。

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

lemma appendRight_prepend (w : List I) (x y z t : D) :
    (C.prependMap A D I w x y z ▷ C.internalHom A D I z t) ≫ C.appendRight A D I w x z t =
    (α_ (homObject A D x y) (C.term A D I w y z) (C.internalHom A D I z t)).hom ≫
      (homObject A D x y) ◁ C.appendRight A D I w y z t ≫ C.internalPrepend A D I x y t := by
  apply (tensorLeftCoproductIsColimit (homObject A D x y ⊗ C.term A D I w y z)
    (fun v : List I => C.term A D I v z t)).hom_ext
  rintro ⟨v⟩
  change ((homObject A D x y ⊗ C.term A D I w y z) ◁ C.inclusion A D I v z t) ≫
      (C.prependMap A D I w x y z ▷ C.internalHom A D I z t) ≫ C.appendRight A D I w x z t =
    ((homObject A D x y ⊗ C.term A D I w y z) ◁ C.inclusion A D I v z t) ≫
      (α_ (homObject A D x y) (C.term A D I w y z) (C.internalHom A D I z t)).hom ≫
      (homObject A D x y) ◁ C.appendRight A D I w y z t ≫ C.internalPrepend A D I x y t
  rw [whisker_exchange_assoc, appendRight_inclusion, appendMap_prepend_assoc,
    associator_naturality_right_assoc, ← whiskerLeft_comp_assoc, appendRight_inclusion,
    whiskerLeft_comp_assoc, internalPrepend_inclusion]

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
