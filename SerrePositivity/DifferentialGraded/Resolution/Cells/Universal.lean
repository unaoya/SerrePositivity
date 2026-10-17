module
public import SerrePositivity.DifferentialGraded.Resolution.Cells.Reconstruction

/-! # 元のdg関手と指定生成cellの像による延長の一意性

## 概要
元のdg関手と指定生成cellの像による延長の一意性。

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
universe u v w z
namespace SerrePositivity.DifferentialGraded.DGCellAttachment.Family
open CategoryTheory
variable {A : Type u} [CommRing A] {D : Type v} [DGCategory A D] {I : Type w}
  {C : Family A D I} {E : Type z} [DGCategory A E]

lemma PrimitiveData.hext {F G : DGFunctor A D E}
    (P : PrimitiveData A D I C E F) (Q : PrimitiveData A D I C E G)
    (hF : F = G) (hp : HEq P.primitive Q.primitive) : HEq P Q := by
  cases hF
  apply heq_of_eq
  have hp' := eq_of_heq hp
  cases P
  cases Q
  cases hp'
  rfl

variable [Small.{u} I]

lemma PrimitiveData.extension_congr {F G : DGFunctor A D E}
    (P : PrimitiveData A D I C E F) (Q : PrimitiveData A D I C E G)
    (hF : F = G) (hp : HEq P.primitive Q.primitive) : P.extension = Q.extension := by
  have h := P.hext Q hF hp
  cases hF
  have he := eq_of_heq h
  cases he
  rfl

variable (A D I C)

lemma extension_unique {F : DGFunctor A D E} (P : PrimitiveData A D I C E F)
    (G : DGFunctor A (C.Objects A D I) E) (hF : C.restrictFunctor A D I G = F)
    (hp : HEq (C.restrictPrimitives A D I G).primitive P.primitive) : G = P.extension :=
  (C.extension_restrict A D I G).symm.trans
    ((C.restrictPrimitives A D I G).extension_congr P hF hp)

lemma functor_ext (G H : DGFunctor A (C.Objects A D I) E)
    (hF : C.restrictFunctor A D I G = C.restrictFunctor A D I H)
    (hp : HEq (C.restrictPrimitives A D I G).primitive
      (C.restrictPrimitives A D I H).primitive) : G = H :=
  (C.extension_restrict A D I G).symm.trans
    (((C.restrictPrimitives A D I G).extension_congr (C.restrictPrimitives A D I H) hF hp).trans
      (C.extension_restrict A D I H))

end SerrePositivity.DifferentialGraded.DGCellAttachment.Family
