module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.TensorPathCochainExt
public import SerrePositivity.DifferentialGraded.Resolution.Cells.TensorRightPathCochainExt

/-! # 二つの全path直和のtensorからの任意次数cochainの判定

## 概要
二つの全path直和のtensorからの任意次数cochainの判定。

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

lemma tensorTwoPathCochain_ext (x y z : D) {T : Complex A} (p : ℤ)
    (f g : Cochain (C.internalHom A D I x y ⊗ C.internalHom A D I y z) T p)
    (h : ∀ w v : List I,
      (Cochain.ofHom (C.inclusion A D I w x y ⊗ₘ C.inclusion A D I v y z)).comp f
      (zero_add p) =
      (Cochain.ofHom (C.inclusion A D I w x y ⊗ₘ C.inclusion A D I v y z)).comp g (zero_add p)) :
    f = g := by
  apply C.tensorRightPathCochain_ext A D I x y (C.internalHom A D I y z) p
  intro w
  apply C.tensorLeftPathCochain_ext A D I y z (C.term A D I w x y) p
  intro v
  simpa only [← Cochain.comp_assoc_of_first_is_zero_cochain, ← Cochain.ofHom_comp,
    ← tensorHom_def'] using h w v

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
