module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.PathAction
public import SerrePositivity.DifferentialGraded.Complexes.TensorCoproduct

/-! # cell pathの連結を内部Hom直和へ延長した合成

## 概要
cell pathの連結を内部Hom直和へ延長した合成。

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
open CategoryTheory Limits MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w) [Small.{u} I]
variable (C : Family A D I)

def internalComposition (x y z : D) :
    C.internalHom A D I x y ⊗ C.internalHom A D I y z ⟶ C.internalHom A D I x z :=
  tensorCoproductDesc (fun w : List I => C.term A D I w x y)
    (fun v : List I => C.term A D I v y z) (C.internalHom A D I x z)
    (fun w v => C.appendMap A D I w v x y z ≫ C.inclusion A D I (w ++ v) x z)

lemma internalComposition_inclusion (x y z : D) (w v : List I) :
    (C.inclusion A D I w x y ⊗ₘ C.inclusion A D I v y z) ≫ C.internalComposition A D I x y z =
      C.appendMap A D I w v x y z ≫ C.inclusion A D I (w ++ v) x z :=
  tensorCoproductDesc_ι _ _ _ _ w v

lemma internalComposition_original_left (x y z : D) (w : List I) :
    (C.originalHom A D I x y ⊗ₘ C.inclusion A D I w y z) ≫ C.internalComposition A D I x y z =
      C.prependMap A D I w x y z ≫ C.inclusion A D I w x z :=
  C.internalComposition_inclusion A D I x y z [] w

lemma internalComposition_original_original (x y z : D) :
    (C.originalHom A D I x y ⊗ₘ C.originalHom A D I y z) ≫ C.internalComposition A D I x y z =
      eComp (Complex A) x y z ≫ C.originalHom A D I x z :=
  C.internalComposition_inclusion A D I x y z [] []

def appendRight (w : List I) (x y z : D) :
    C.term A D I w x y ⊗ C.internalHom A D I y z ⟶ C.internalHom A D I x z :=
  tensorCoproductRightDesc (C.term A D I w x y) (fun v : List I => C.term A D I v y z)
    (C.internalHom A D I x z)
    (fun v => C.appendMap A D I w v x y z ≫ C.inclusion A D I (w ++ v) x z)

lemma appendRight_inclusion (w v : List I) (x y z : D) :
    (C.term A D I w x y ◁ C.inclusion A D I v y z) ≫ C.appendRight A D I w x y z =
      C.appendMap A D I w v x y z ≫ C.inclusion A D I (w ++ v) x z :=
  tensorCoproductRightDesc_ι _ _ _ _ v

lemma internalComposition_left_inclusion (w : List I) (x y z : D) :
    (C.inclusion A D I w x y ▷ C.internalHom A D I y z) ≫ C.internalComposition A D I x y z =
      C.appendRight A D I w x y z := tensorCoproductDesc_left _ _ _ _ w

abbrev internalPrepend (x y z : D) :
    homObject A D x y ⊗ C.internalHom A D I y z ⟶ C.internalHom A D I x z :=
  C.appendRight A D I [] x y z

lemma internalPrepend_inclusion (x y z : D) (w : List I) :
    (homObject A D x y ◁ C.inclusion A D I w y z) ≫ C.internalPrepend A D I x y z =
      C.prependMap A D I w x y z ≫ C.inclusion A D I w x z :=
  C.appendRight_inclusion A D I [] w x y z

def internalIdentity (x : D) : 𝟙_ (Complex A) ⟶ C.internalHom A D I x x :=
  eId (Complex A) x ≫ C.originalHom A D I x x

lemma internalComposition_left_unit (x y : D) :
    (λ_ (C.internalHom A D I x y)).inv ≫
      C.internalIdentity A D I x ▷ C.internalHom A D I x y ≫
      C.internalComposition A D I x x y = 𝟙 _ := by
  apply C.internalHom_ext A D I x y
  intro w
  simp only [internalIdentity, comp_whiskerRight, Category.assoc, Category.comp_id]
  rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc, whisker_exchange_assoc,
    ← tensorHom_def_assoc, internalComposition_original_left]
  rw [reassoc_of% (C.prependMap_left_unit A D I w x y)]

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
