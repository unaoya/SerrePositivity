module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Paths

/-! # 生成cellのpathと既存Homの合成

## 概要
生成元の順を保ち、隣り合う既存Homだけを豊穣合成する。

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
universe u v w
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory MonoidalCategory
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] (I : Type w)
variable (C : Family A D I)

def prependMap : ∀ (w : List I) (x y z : D),
    homObject A D x y ⊗ C.term A D I w y z ⟶ C.term A D I w x z
  | [], x, y, z => eComp (Complex A) x y z
  | i :: w, x, y, z =>
    (α_ (homObject A D x y) (homObject A D y (C.source i))
      (C.generator A D I i ⊗ C.term A D I w (C.target i) z)).inv ≫
      (eComp (Complex A) x y (C.source i) ⊗ₘ
        𝟙 (C.generator A D I i ⊗ C.term A D I w (C.target i) z))

def appendMap : ∀ (w z : List I) (x y t : D),
    C.term A D I w x y ⊗ C.term A D I z y t ⟶ C.term A D I (w ++ z) x t
  | [], z, x, y, t => C.prependMap A D I z x y t
  | i :: w, z, x, y, t =>
    (α_ (homObject A D x (C.source i))
      (C.generator A D I i ⊗ C.term A D I w (C.target i) y)
      (C.term A D I z y t)).hom ≫
    (homObject A D x (C.source i)) ◁
      ((α_ (C.generator A D I i) (C.term A D I w (C.target i) y)
        (C.term A D I z y t)).hom ≫
        (C.generator A D I i) ◁ appendMap w z (C.target i) y t)

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
