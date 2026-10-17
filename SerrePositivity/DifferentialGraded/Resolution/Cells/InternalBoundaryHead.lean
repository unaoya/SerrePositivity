module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PrependBoundary
public import SerrePositivity.DifferentialGraded.Complexes.TensorCarryCochain

/-! # 全path直和に先頭生成元の指定境界を作用させるcochain

## 概要
全path直和に先頭生成元の指定境界を作用させるcochain。

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

def internalReplaceHead (b : I) (y : D) :
    Cochain (C.generator A D I b ⊗ C.internalHom A D I (C.target b) y)
      (C.internalHom A D I (C.source b) y) 1 :=
  ((tensorRightHom (C.internalHom A D I (C.target b) y) _ _).f 1
    (C.boundaryCochain A D I b)).comp
    (Cochain.ofHom (C.internalPrepend A D I (C.source b) (C.target b) y)) (add_zero 1)

def internalReplaceFirst (b : I) (x y : D) :
    Cochain (homObject A D x (C.source b) ⊗
      (C.generator A D I b ⊗ C.internalHom A D I (C.target b) y)) (C.internalHom A D I x y) 1 :=
  ((tensorLeftHom (homObject A D x (C.source b)) _ _).f 1
    (C.internalReplaceHead A D I b y)).comp
    (Cochain.ofHom (C.internalPrepend A D I x (C.source b) y)) (add_zero 1)

lemma internalReplaceHead_inclusion (b : I) (w : List I) (y : D) :
    (Cochain.ofHom ((C.generator A D I b) ◁ C.inclusion A D I w (C.target b) y)).comp
      (C.internalReplaceHead A D I b y) (zero_add 1) =
    (C.replaceHead A D I b w y).comp
      (Cochain.ofHom (C.inclusion A D I w (C.source b) y)) (add_zero 1) := by
  rw [internalReplaceHead, replaceHead, ← Cochain.comp_assoc_of_first_is_zero_cochain,
    tensorRight_cochain_chain_naturality, Cochain.comp_assoc_of_third_is_zero_cochain,
    ← Cochain.ofHom_comp, internalPrepend_inclusion]
  rw [Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp]

lemma internalReplaceFirst_inclusion (b : I) (w : List I) (x y : D) :
    (Cochain.ofHom ((homObject A D x (C.source b)) ◁
      ((C.generator A D I b) ◁ C.inclusion A D I w (C.target b) y))).comp
      (C.internalReplaceFirst A D I b x y) (zero_add 1) =
    (C.replaceFirst A D I b w x y).comp
      (Cochain.ofHom (C.inclusion A D I w x y)) (add_zero 1) := by
  rw [internalReplaceFirst, replaceFirst_eq_head,
    ← Cochain.comp_assoc_of_first_is_zero_cochain,
    ← tensorLeftHom_ofHom (homObject A D x (C.source b)),
    ← tensorLeftHom_cochain_comp, internalReplaceHead_inclusion,
    tensorLeftHom_cochain_comp, tensorLeftHom_ofHom,
    Cochain.comp_assoc_of_third_is_zero_cochain,
    Cochain.comp_assoc_of_third_is_zero_cochain, ← Cochain.ofHom_comp, ← Cochain.ofHom_comp,
    internalPrepend_inclusion]

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
