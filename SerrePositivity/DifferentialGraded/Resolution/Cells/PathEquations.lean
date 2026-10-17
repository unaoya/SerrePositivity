module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Paths

/-! # cell path項の計算式

## 概要
未知の後続語の再帰定義を展開せず、先頭一段だけを計算する。

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

lemma term_nil (x y : D) : C.term A D I [] x y = homObject A D x y := rfl

lemma term_cons (b : I) (w : List I) (x y : D) :
    C.term A D I (b :: w) x y = homObject A D x (C.source b) ⊗
      (C.generator A D I b ⊗ C.term A D I w (C.target b) y) := rfl

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
