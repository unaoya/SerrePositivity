module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.InternalBoundaryHead
public import SerrePositivity.DifferentialGraded.Resolution.Cells.AppendRightPrepend

/-! # 後続pathの連結と先頭生成元の境界置換の整合性

## 概要
後続pathの連結と先頭生成元の境界置換の整合性。

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
attribute [local irreducible] internalReplaceHead internalReplaceFirst replaceHead replaceFirst

lemma appendRight_replaceHead (b : I) (w : List I) (y z : D) :
    (Cochain.ofHom ((α_ (C.generator A D I b) (C.term A D I w (C.target b) y)
      (C.internalHom A D I y z)).hom ≫
      (C.generator A D I b) ◁ C.appendRight A D I w (C.target b) y z)).comp
      (C.internalReplaceHead A D I b z) (zero_add 1) =
    ((tensorRightHom (C.internalHom A D I y z) _ _).f 1
      (C.replaceHead A D I b w y)).comp
      (Cochain.ofHom (C.appendRight A D I w (C.source b) y z)) (add_zero 1) := by
  unfold internalReplaceHead replaceHead
  exact tensorRight_action_cochain (C.generator A D I b)
    (homObject A D (C.source b) (C.target b)) _ _ _ _ _ 1 (C.boundaryCochain A D I b)
    (C.appendRight A D I w (C.target b) y z)
    (C.prependMap A D I w (C.source b) (C.target b) y)
    (C.appendRight A D I w (C.source b) y z)
    (C.internalPrepend A D I (C.source b) (C.target b) z)
    (C.appendRight_prepend A D I w (C.source b) (C.target b) y z)

lemma appendRight_replaceFirst (b : I) (w : List I) (x y z : D) :
    (Cochain.ofHom ((α_ (homObject A D x (C.source b))
      (C.generator A D I b ⊗ C.term A D I w (C.target b) y) (C.internalHom A D I y z)).hom ≫
      (homObject A D x (C.source b)) ◁
        ((α_ (C.generator A D I b) (C.term A D I w (C.target b) y)
          (C.internalHom A D I y z)).hom ≫
          (C.generator A D I b) ◁ C.appendRight A D I w (C.target b) y z))).comp
      (C.internalReplaceFirst A D I b x z) (zero_add 1) =
    ((tensorRightHom (C.internalHom A D I y z) _ _).f 1
      (C.replaceFirst A D I b w x y)).comp
      (Cochain.ofHom (C.appendRight A D I w x y z)) (add_zero 1) := by
  rw [internalReplaceFirst, replaceFirst_eq_head]
  simpa only [term, whiskerLeft_comp, Category.assoc] using
    tensorCarry_cochain (homObject A D x (C.source b))
      (C.generator A D I b ⊗ C.term A D I w (C.target b) y)
      (C.term A D I w (C.source b) y) (C.internalHom A D I y z)
      (C.generator A D I b ⊗ C.internalHom A D I (C.target b) z)
      (C.internalHom A D I (C.source b) z) (C.term A D I w x y) (C.internalHom A D I x z) 1
    (C.replaceHead A D I b w y) (C.internalReplaceHead A D I b z)
    ((α_ (C.generator A D I b) (C.term A D I w (C.target b) y)
      (C.internalHom A D I y z)).hom ≫
      (C.generator A D I b) ◁ C.appendRight A D I w (C.target b) y z)
    (C.appendRight A D I w (C.source b) y z)
    (C.prependMap A D I w x (C.source b) y)
    (C.internalPrepend A D I x (C.source b) z) (C.appendRight A D I w x y z)
    (C.appendRight_replaceHead A D I b w y z) (C.appendRight_prepend A D I w x (C.source b) y z)

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
